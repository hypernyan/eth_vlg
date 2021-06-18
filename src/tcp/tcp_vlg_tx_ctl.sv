module tcp_vlg_tx_ctl 
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int    MTU                   = 1500,
  parameter int    RETRANSMIT_TICKS      = 1000000,
  parameter int    FAST_RETRANSMIT_TICKS = 10000,
  parameter int    SACK_RETRANSMIT_TICKS = 10000,
  parameter int    RETRANSMIT_TRIES      = 5,
  parameter int    RAM_DEPTH             = 10,
  parameter int    PACKET_DEPTH          = 3,
  parameter int    WAIT_TICKS            = 20,
  parameter bit    VERBOSE               = 0,
  parameter string DUT_STRING            = ""
)
(
  input    logic clk,
  input    logic rst,
  input    dev_t dev,
  tcp_data.in_tx data, // user inteface (raw TCP stream)
  tx_ctl.in      ctl   // engine is connected via this ifc
);

  enum logic [1:0] {idle_s, pend_s}                   w_fsm;
  enum logic [2:0] {tx_idle_s, tx_wait_s, tx_on_s}    tx_fsm;
  enum logic [8:0] {scan_s, choice_s, dup_s, sack_s, dif_s, upd_s, next_s, read_s, flush_s} scan_fsm;

  tcp_pkt_t upd_pkt, upd_pkt_q, new_pkt, new_pkt_q;
  tcp_num_t prev_loc_seq;

  logic [$clog2(MTU+1)-1:0] ctr;
  logic [$clog2(WAIT_TICKS+1)-1:0] timeout;
  logic [31:0] cks;
  logic [31:0] ack_dif;
  logic [7:0] in_d_prev;

  logic add_timeout, add_mtu, add_pend, add, upd, free;

  logic [PACKET_DEPTH-1:0]  flush_ctr, next_ptr;
  logic [PACKET_DEPTH:0] add_ptr, upd_ptr, rem_ptr, info_space;

  logic [RAM_DEPTH-1:0] space, buf_addr;
  logic [7:0]           buf_data;

  length_t tx_byte_cnt;
  logic buf_rst;

  logic fast_rtx, pend, send, clr_last;
 
  logic tx_idle;
  logic [31:0] diff_seq; 
  logic upd_last_seq;

  logic unsacked;
  tcp_opt_sack_t sack;
  logic [31:0] start_dif, stop_dif;
  logic [1:0] sack_ctr;
  logic sack_rtx;
  logic norm_tx; 
  logic long_rtx;
  
  logic [31:0] dup_start_dif;
  logic [31:0] dup_stop_dif;
  logic dup_det;
  logic acked;
  
  tcp_num_t last_ack;

  //////////////////////////////
  // Transmission data buffer //
  //////////////////////////////
  always_ff @ (posedge clk) buf_rst <= ctl.init;

  tcp_vlg_tx_buf #(
    .D (RAM_DEPTH),
    .W (8)
  ) tcp_vlg_tx_buf_inst (
    .rst (buf_rst),
    .clk (clk),

    .write    (data.val), // user data valid
    .data_in  (data.dat), // user data valid
    .seq      (ctl.loc_seq),   // local seqence number
    
    .ack      (last_ack),  // highest recorded remote ack number 
    .addr     (buf_addr), // address to read from
    .data_out (buf_data), // data at 'addr' (1 tick delay)


    .space    (space),        // space left in buffer
    .f (full),
    .e (empty)
  );

  /////////////////////
  // Packet info RAM //
  /////////////////////

  ram_if_dp #(
    .AW (PACKET_DEPTH),
    .DW ($bits(tcp_pkt_t))
  ) info (.*);

  ram_dp #(
    .AW (PACKET_DEPTH),
    .DW ($bits(tcp_pkt_t))
  ) data_ram_inst (info);

  assign info.clk_a = clk;
  assign info.clk_b = clk;
  assign info.rst   = rst;
  // `Add new packet` port
  assign info.a_a   = add_ptr[PACKET_DEPTH-1:0];
  assign info.d_a   = new_pkt;
  assign info.w_a   = add;
  // `Update of remove existing packet`
  assign info.a_b   = upd_ptr[PACKET_DEPTH-1:0];
  assign info.d_b   = upd_pkt;
  assign info.w_b   = upd;
  assign upd_pkt_q  = info.q_b;

  // difference between push and pop ptr indicate the space left for
  // individual packets that may be stored in packet info RAM
  assign info_space = add_ptr - rem_ptr + 1; // -1 to get correct full flag (no overwriting when full)

  // clear to send flag is set if:
  // 1. tcp is connected
  // 2. packet info RAM isn't full (check msb)
  // 3. transmission data buffer isn't full ()
  assign data.cts = (ctl.status == tcp_connected) && !info_space[PACKET_DEPTH] && !full;

  // New data for transmission didn't arrive for WAIT_TICKS
  assign add_timeout = (timeout == WAIT_TICKS && !data.val);
  // Packet length reached MTU
  assign add_mtu = (ctr == MTU - 80 - 1); // 60 for tcp header (with options) and another 20 for ipv4. todo: check for correctness

  assign add_pend = (w_fsm == pend_s) && (add_timeout || add_mtu || full || data.snd);   
  assign new_pkt.length   = ctr; // length equals byte count for current packet
  assign new_pkt.cks      = ctr[0] ? cks + {in_d_prev, 8'h00} : cks; // this is how payadd checksum is calculated
  assign new_pkt.exists     = 1;                     // Every new entry in packet info table is ofc valid
  assign new_pkt.tries    = 0;                     // The packet hasn't been transmittd yet
   assign new_pkt.norm_rto = 0;      // preadd so packet is read out asap the first time
  assign new_pkt.sack_rto = 0; // preadd so packet is read out asap the first time
  assign new_pkt.stop     = ctl.loc_seq;           // equals expected ack for packet

  // Sequence number tracker
  always_ff @ (posedge clk) begin
    if (ctl.rst) ctl.loc_seq <= 0;
    else begin
      if (ctl.init) ctl.loc_seq <= ctl.tcb.loc_seq; // initialize current seq at connection reset;
      else if (data.val) ctl.loc_seq <= ctl.loc_seq + 1;
    end
  end

  // Packet creation FSM
  always_ff @ (posedge clk) begin
    if (ctl.rst) begin
      ctr      <= 0;
      add_ptr <= 0;
      add     <= 0;
      timeout  <= 0;
      w_fsm    <= idle_s;
    end
    else begin
      if (data.val) in_d_prev <= data.dat;
      case (w_fsm)
        idle_s : begin
          if (data.val) begin
            ctr   <= 1;
            w_fsm <= pend_s;
          end
          prev_loc_seq <= ctl.loc_seq; // equals packet's seq
          add     <= 0;
          cks     <= 0;
          timeout <= 0;
        end
        pend_s : begin
         // pend <= 0;
          new_pkt.start <= prev_loc_seq;
          if (data.val) begin
            ctr <= ctr + 1;
            cks <= (ctr[0]) ? cks + {in_d_prev, data.dat} : cks;
          end
          timeout <= (data.val) ? 0 : timeout + 1; // reset timeout if new byte arrives
          // either of three conditions to add new packet
          if (full || add_timeout || add_mtu || data.snd) w_fsm <= idle_s;
        end
      endcase
      add <= (add_pend && !ctl.flush); // add packet 1 tick after 'add_pend'
      if (add) add_ptr <= add_ptr + 1;
    end
  end

  always_ff @ (posedge clk) begin
    if (ctl.rst || ctl.init) begin // Engine has to close connection to reenable ctl
      scan_fsm      <= scan_s;
      upd           <= 0;
      rem_ptr       <= 0;
      upd_ptr       <= 0;
      next_ptr      <= 0;
      ctl.force_dcn <= 0;
      ctl.flushed   <= 0;
      ctl.pld_info  <= 0;
      flush_ctr     <= 0;
      upd_pkt       <= 0;
      free          <= 0;
      pend          <= 0;
      ack_dif       <= 0;
      fast_rtx      <= 0;
      sack_ctr      <= 0;
      norm_tx       <= 0;
      sack_rtx      <= 0;
      long_rtx      <= 0;
      last_ack      <= ctl.tcb.rem_ack;
    end
    else begin
      case (scan_fsm)
        scan_s : begin
          sack_ctr    <= 0;
          sack        <= ctl.tcb.rem_sack; // latch current remote sack
          upd_pkt     <= upd_pkt_q;
          unsacked    <= 0;
          send        <= 0;
          upd         <= 0;
          ctl.flushed <= 0;
          free        <= 0;
          norm_tx     <= 0; 
          sack_rtx    <= 0;
          fast_rtx    <= 0;
          long_rtx    <= 0;
          // continiously scan for unacked packets. If present flag found, check if it's acked and if it's ready for transmission
          // if packet at current address is not present, read next one and so on
          scan_fsm <= (ctl.flush) ? flush_s : dup_s;
            // this diference defines if packed is acked
            // latch all info on this packet before continuing
            // decision to transmit will be made later
          ack_dif <= ctl.tcb.rem_ack - upd_pkt_q.stop; // bit[31] means packet is acked (pkt's last seq < remote_ack)
        end
        // choose 
        dup_s : begin
          acked         <= upd_pkt.exists && !ack_dif[31];// !ack_dif[31] means packet is acked by remote host completely and may be removed (free space)
          scan_fsm      <= dif_s;
          dup_det       <= ctl.dup_det;
          dup_start_dif <= ctl.dup_ack - upd_pkt.start;
          dup_stop_dif  <= upd_pkt.stop - ctl.dup_ack;
        end
        sack_s : begin // choose to fast retransmit if packet isn't sacked
          // retransmit a packet if at least part of it is not contained within any sack block.
          // the decision is made if the packet exceeds any border of any block
          // if no sack blocks are present, 'unsacked' stays 0 and will not fast retranmsit
          if (sack.block_pres[0] && (start_dif[31] || stop_dif[31])) unsacked <= 1; // if packet is not contained within any present sack block.
          sack.block_pres[0:3] <= {sack.block_pres[1:3], 1'b0};
          if (sack_ctr == 3) scan_fsm <= choice_s;
          else begin
            sack_ctr <= sack_ctr + 1;
            scan_fsm <= dif_s;
          end
        end
        // calculate 
        dif_s : begin
          sack.block[0:2] <= sack.block[1:3];
          start_dif <= sack.block[0].right - upd_pkt.stop;   // [31] means |==block===]r-----------|==>+----+
                                                             //            |=====pkt===]?stop?]----|   | Or |==> sack retransmit
          stop_dif  <= upd_pkt.start   - sack.block[0].left; // [31] means |----------l[===block===|==>|    |
                                                             //            |--[?start?[============|   +----+ 
          scan_fsm <= sack_s;
        end
        // choose what to do with an entry
        choice_s : begin
          if (acked) begin
            if (upd_ptr == rem_ptr) free <= 1;
          end
          else if (upd_pkt.exists && (ctl.tcb.wnd_scl >= MTU) && tx_idle) begin
            // only transmit if packet isn't acked, timer reached timeout and there are no pending transmissions
  		      norm_tx  <= !dup_det && (upd_pkt.tries == 0) && (upd_ptr == next_ptr); // normal transmission is forced in-order
  		      sack_rtx <= !dup_det && (upd_pkt.sack_rto == SACK_RETRANSMIT_TICKS) && unsacked;
            fast_rtx <=  dup_det && !dup_start_dif[31] && !dup_stop_dif[31]  && (upd_pkt.tries == 1); // check if this packet contains the dup ack to fast rtx it
            long_rtx <= (upd_pkt.norm_rto == RETRANSMIT_TICKS); // last resort retransmission
          end
          if (upd_pkt.tries == RETRANSMIT_TRIES) ctl.force_dcn <= 1; // force disconnect if there were too many retransmission attempts
          else if (!add_pend) scan_fsm <= upd_s; // avoid collision with port A
        end
        // update entries
        upd_s : begin
          scan_fsm <= next_s;
          upd      <= upd_pkt.exists; // update packed info
          // Will be clearting packet cause it's acked
          if (free) begin
            last_ack       <= upd_pkt.stop; // use this as 'read pointer' in data RAM. free space up to this number
            rem_ptr        <= rem_ptr + 1;
            upd_pkt.exists <= 0;
          end
          // Will be transmitting
          else if (norm_tx || sack_rtx || fast_rtx || long_rtx) begin
            ctl.pld_info.start <= upd_pkt.start;
            ctl.pld_info.stop  <= upd_pkt.stop;
 	          ctl.pld_info.lng   <= upd_pkt.length;
       	    ctl.pld_info.cks   <= upd_pkt.cks;
            if (VERBOSE) begin
              if (upd_pkt.tries > 0) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d-> TCP retransmission try %d to %d.%d.%d.%d:%d Seq=%d, Len=%d",
                dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], ctl.tcb.loc_port,
                upd_pkt.tries,
                ctl.tcb.ipv4_addr[3], ctl.tcb.ipv4_addr[2], ctl.tcb.ipv4_addr[1], ctl.tcb.ipv4_addr[0], ctl.tcb.rem_port,
                upd_pkt.start, upd_pkt.length
              );
            end
            if (norm_tx) next_ptr <= upd_ptr + 1;
            send <= 1;
            upd_pkt.exists   <= 1; // packet is still stored
            upd_pkt.tries    <= upd_pkt.tries + 1; // try count incremented
            upd_pkt.norm_rto <= 0;
            upd_pkt.sack_rto <= 0; // retransmitting packet. reset sack_rto
            // before retransmitting packets, set pointer to this packet
            // because we want so send (even retransmit) packets in order
            // and they are stored in info RAM naturally
            // that way
            // continuing retransmissions from this pointer will guarantee that
          end
          // will increment 
          else begin
            upd_pkt.tries <= upd_pkt.tries;
            upd_pkt.exists   <= upd_pkt.exists; // packet is still stored
            if (upd_pkt.norm_rto != RETRANSMIT_TICKS)      upd_pkt.norm_rto <= upd_pkt.norm_rto + 1; // increment
            if (upd_pkt.sack_rto != SACK_RETRANSMIT_TICKS) upd_pkt.sack_rto <= upd_pkt.sack_rto + 1; // increment
            //if (fast_rtx) upd_pkt.norm_rto <= RETRANSMIT_TICKS;
          end
        end
        next_s : begin
          upd_ptr  <= upd_ptr + 1;
          upd      <= 0;
          scan_fsm <= read_s;
        end
        read_s : begin
          scan_fsm <= scan_s;
        end
        // Flush only info RAM
        // Data RAM may be kept intact and will be lost
        flush_s : begin
          send           <= 0;
          upd_pkt.exists <= 0; // resetting present flag in all entries is sufficient to flush info RAM
          upd            <= 1;
          upd_ptr        <= upd_ptr + 1;
          flush_ctr      <= flush_ctr + 1;
          if (flush_ctr == 0 && upd && tx_idle) ctl.flushed <= 1; // wait for tx to finish 
        end
      endcase
    end
  end

  ///////////////////////
  // tx management FSM //
  ///////////////////////

  // remote host may acknowledge some part of the packet (mainly when sending payadd of length > remote host window)
  // ctl RAM frees space based on ack_num
  // have to check if received ack_num acknowledges whole packet, otherwise data may be corrupted due to incorrect release
  // pass packet's expected ack instead of actual received ack which acknowledges packet containing that 

  // - free space         p s      r a          p a
  // = valid data         k e      e c          k c
  // x overwritten data   t q      m k          t k
  //                   ----|=====================|---- 
  //                   ----|========|xxxxxxxxxxxx|---- data loss if remote ack is passed directly to ctl RAM

  // decide if last sent seq num update is needed
  // check for overflow for correct operation

  // compare start/stop with remote ack
  // and decide if packet is 
  // - fully acked and may be discarded
  // - partially of completely acked and must be kept or retransmitted
  

  always_ff @ (posedge clk) begin
    if (ctl.rst || ctl.init) begin
      tx_fsm       <= tx_idle_s;
      ctl.send     <= 0;
      tx_idle      <= 1;
      ctl.last_seq <= ctl.tcb.loc_seq;
      buf_addr     <= ctl.tcb.loc_seq;
      ctl.strm.val <= 0;
      ctl.strm.sof <= 0;
      ctl.strm.eof <= 0;
      tx_byte_cnt  <= 0;
    end
    else begin
      case (tx_fsm)
        tx_idle_s : begin
          diff_seq <= upd_pkt.stop - ctl.last_seq;
          tx_byte_cnt <= 0;
          if (send) begin
            buf_addr <= ctl.pld_info.start[RAM_DEPTH-1:0];
            tx_idle <= 0;
            tx_fsm <= tx_wait_s;
            ctl.send <= 1;
          end
          else tx_idle <= 1;
        end
        tx_wait_s : begin
          upd_last_seq <= !diff_seq[31]; // only update last seq if packet's end it's above current local seq
          if (ctl.req) begin
            ctl.send     <= 0;
            ctl.strm.sof <= 1;
            ctl.strm.val <= 1;
            buf_addr <= buf_addr + 1;
            tx_fsm <= tx_on_s;
          end
        end
        tx_on_s : begin
          tx_byte_cnt <= tx_byte_cnt + 1;
          buf_addr <= buf_addr + 1;
          ctl.strm.sof <= 0;
          if (ctl.strm.eof) ctl.strm.val <= 0;
          ctl.strm.eof <= (tx_byte_cnt == ctl.pld_info.lng - 1);
          if (ctl.sent) begin // tx logic indicates packet was sent
            if (upd_last_seq) ctl.last_seq <= ctl.pld_info.stop; // Update last seq that was actually sent
            tx_fsm <= tx_idle_s;
          end
        end
      endcase
    end
  end
  assign ctl.strm.dat = buf_data;
endmodule : tcp_vlg_tx_ctl
