module tcp_vlg_tx_scan
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int    MTU                   = 1500,
  parameter int    RETRANSMIT_TICKS      = 1000000,
  parameter int    SACK_RETRANSMIT_TICKS = 10000,
  parameter int    RETRANSMIT_TRIES      = 5,
  parameter int    PACKET_DEPTH          = 3,
  parameter bit    VERBOSE               = 0,
  parameter string DUT_STRING            = ""
)
(
  input    logic clk,
  input    logic rst,
  input    dev_t dev,
  input    tcb_t tcb,
  input    logic add_pend,
  // info ram interface
  output logic                    upd,
  output logic                    free,
  output logic [PACKET_DEPTH-1:0] ptr,
  input  tcp_pkt_t                pkt_r,
  output tcp_pkt_t                pkt_w,

  output tcp_num_t                last_ack,   // highest recorded remote ack
  output tcp_pld_info_t           pld_info,  // payload info for tx module
  output logic                    pend,
  output logic                    force_dcn, // request to abort connection (failed rtx)
  input  logic                    flush,     // engine's request to flush info ram
  output logic                    flushed,   // indicates that info ram is flushed
  input  logic                    dup_det,   // duplicate ack detected
  input  tcp_num_t                dup_ack,    // duplicate ack number
  input  logic                    tx_idle
);
  enum logic [8:0] {scan_s, choice_s, dup_s, sack_s, dif_s, upd_s, next_s, read_s, flush_s} fsm;

  logic [PACKET_DEPTH-1:0] flush_ctr, next_ptr;
  logic unsacked;
  logic acked;
  tcp_opt_sack_t sack;
  logic [31:0] start_dif, stop_dif;
  logic [31:0] dup_start_dif, dup_stop_dif;
  logic [1:0] sack_ctr;
  logic sack_rtx;
  logic norm_tx; 
  logic long_rtx;
  logic dup_det_reg;
  logic [31:0] ack_dif;
  logic fast_rtx;
  logic norm_rtx;

  always_ff @ (posedge clk) begin
    if (rst) begin // Engine has to close connection to reenable ctl
      fsm       <= scan_s;
      upd       <= 0;
      ptr   <= 0;
      next_ptr  <= 0;
      force_dcn <= 0;
      flushed   <= 0;
      pld_info  <= 0;
      flush_ctr <= 0;
      pkt_w     <= 0;
      free      <= 0;
      ack_dif   <= 0;
      fast_rtx  <= 0;
      sack_ctr  <= 0;
      norm_tx   <= 0;
      sack_rtx  <= 0;
      norm_rtx  <= 0;
      long_rtx  <= 0;
      pend      <= 0;
      last_ack  <= tcb.rem_ack;
    end
    else begin
      case (fsm)
        scan_s : begin
          sack_ctr <= 0;
          sack     <= tcb.rem_sack; // latch current remote sack
          pkt_w    <= pkt_r;
          unsacked <= 0;
          pend     <= 0;
          upd      <= 0;
          flushed  <= 0;
          free     <= 0;
          norm_tx  <= 0; 
          sack_rtx <= 0;
          fast_rtx <= 0;
          norm_rtx <= 0;
          // continiously scan for unacked packets. If present flag found, check if it's acked and if it's ready for transmission
          // if packet at current address is not present, read next one and so on
          fsm <= (flush) ? flush_s : dup_s;
          // this difference defines if packed is acked
          ack_dif <= tcb.rem_ack - pkt_r.stop; // bit[31] means packet is acked (pkt's last seq < remote_ack)
        end
        // choose 
        dup_s : begin
          acked         <= pkt_w.exists && !ack_dif[31];// !ack_dif[31] means packet is acked by remote host completely and may be removed (free space)
          fsm           <= dif_s;
          dup_det_reg   <= dup_det;
          dup_start_dif <= dup_ack - pkt_w.start;
          dup_stop_dif  <= pkt_w.stop - dup_ack;
        end
        sack_s : begin // choose to fast retransmit if packet isn't sacked
          // retransmit a packet if at least part of it is not contained within any sack block.
          // the decision is made if the packet exceeds any border of any block
          // if no sack blocks are present, 'unsacked' stays 0 and will not fast retranmsit
          if (sack.block_pres[0] && (start_dif[31] || stop_dif[31])) unsacked <= 1; // if packet is not contained within any present sack block.
          sack.block_pres[0:3] <= {sack.block_pres[1:3], 1'b0};
          if (sack_ctr == 3) fsm <= choice_s;
          else begin
            sack_ctr <= sack_ctr + 1;
            fsm <= dif_s;
          end
        end
        // calculate 
        dif_s : begin
          sack.block[0:2] <= sack.block[1:3];
          start_dif <= sack.block[0].right - pkt_w.stop;   // [31] means |==block===]r-----------|==>+----+
                                                           //            |=====pkt===]?stop?]----|   | Or |==> sack retransmit
          stop_dif  <= pkt_w.start - sack.block[0].left;   // [31] means |----------l[===block===|==>|    |
                                                           //            |--[?start?[============|   +----+ 
          fsm <= sack_s;
        end
        // choose what to do with an entry
        choice_s : begin
          if (pkt_w.exists && (tcb.wnd_scl >= MTU) && tx_idle) begin
            // only transmit if packet isn't acked, timer reached timeout and there are no pending transmissions
  		      norm_tx  <= !dup_det && (pkt_w.tries == 0) && (ptr == next_ptr); // normal transmission is forced in-order
  		      sack_rtx <= !dup_det && (pkt_w.sack_rto == SACK_RETRANSMIT_TICKS) && unsacked; // will retransmit due to SACK block received
            fast_rtx <=  dup_det && !dup_start_dif[31] && !dup_stop_dif[31]  && (pkt_w.tries == 1); // check if this packet contains the dup ack to fast rtx it
            norm_rtx <= (pkt_w.norm_rto == RETRANSMIT_TICKS); // last resort retransmission
          end
          if (pkt_w.tries == RETRANSMIT_TRIES) force_dcn <= 1; // force disconnect if there were too many retransmission attempts
          if (!add_pend) begin
            fsm <= upd_s; // avoid collision with port A
            free <= (acked && pkt_w.start == last_ack); // remove one after another
          end
        end
        // update entry
        upd_s : begin
          fsm <= next_s;
          upd <= pkt_w.exists; // update packed info
          // Will be clearting packet cause it's acked
          free <= 0;
          if (free) begin
            last_ack     <= pkt_w.stop; // use this as 'read pointer' in data RAM. free space up to this number
            pkt_w.exists <= 0;
          end
          // Will be transmitting
          else if (norm_tx || sack_rtx || fast_rtx || norm_rtx) begin
            pld_info.start <= pkt_w.start;
            pld_info.stop  <= pkt_w.stop;
 	          pld_info.lng   <= pkt_w.length;
       	    pld_info.cks   <= pkt_w.cks;
            if (VERBOSE) begin
              if (pkt_w.tries > 0) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d-> TCP retransmission try %d to %d.%d.%d.%d:%d Seq=%d, Len=%d",
                dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
                pkt_w.tries,
                tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
                pkt_w.start, pkt_w.length
              );
            end
            if (norm_tx) next_ptr <= ptr + 1; // next packet to be transmitted in order
            pend <= 1;
            pkt_w.exists   <= 1; // packet is still stored
            pkt_w.tries    <= pkt_w.tries + 1; // try count incremented
            pkt_w.norm_rto <= 0;
            pkt_w.sack_rto <= 0; // retransmitting packet. reset sack_rto
            // before retransmitting packets, set pointer to this packet
            // because we want so send (even retransmit) packets in order
            // and they are stored in info RAM naturally
            // that way
            // continuing retransmissions from this pointer will guarantee that
          end
          // will increment 
          else begin
            pkt_w.tries <= pkt_w.tries;
            pkt_w.exists <= pkt_w.exists; // packet still stored
            if (pkt_w.norm_rto != RETRANSMIT_TICKS)      pkt_w.norm_rto <= pkt_w.norm_rto + 1; // increment
            if (pkt_w.sack_rto != SACK_RETRANSMIT_TICKS) pkt_w.sack_rto <= pkt_w.sack_rto + 1; // increment
          end
        end
        next_s : begin
          ptr <= ptr + 1;
          upd <= 0;
          fsm <= read_s;
        end
        read_s : begin
          fsm <= scan_s;
        end
        // Flush only info RAM
        // Data RAM may be kept intact and will be lost
        flush_s : begin
          pend         <= 0;
          pkt_w.exists <= 0; // resetting present flag in all entries is sufficient to flush info RAM
          upd          <= 1;
          ptr          <= ptr + 1;
          flush_ctr    <= flush_ctr + 1;
          if (flush_ctr == 0 && upd && tx_idle) flushed <= 1; // wait for tx to finish 
        end
      endcase
    end
  end

endmodule
