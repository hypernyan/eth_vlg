import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_tx_ctl #(
  parameter integer MTU              = 1500, // Maximum pld length
  parameter integer RETRANSMIT_TICKS = 1000000,
  parameter integer RETRANSMIT_TRIES = 5,
  parameter integer RAM_DEPTH        = 10,
  parameter integer PACKET_DEPTH     = 3,
  parameter integer WAIT_TICKS       = 20
)
(
  input    logic clk,
  input    logic rst,
  input    dev_t dev,
  tcp_data.in_tx data, // user inteface (raw TCP stream)
  tx_ctl.in      ctl  // tx buffer control
);

  enum logic [2:0] {w_init_s, w_idle_s, w_pend_s} w_fsm;
  
  enum logic [7:0] {
    buf_idle_s,
    buf_scan_s,
    buf_check_s,
    buf_choice_s,
    buf_next_s,
    buf_wait_s,
    buf_retrans_s,
    buf_flush_s
  } fsm;

  tcp_pkt_t upd_pkt, upd_pkt_q, new_pkt, new_pkt_q;

  logic [PACKET_DEPTH-1:0] upd_addr, upd_addr_prev;
  logic [$clog2(MTU+1)-1:0] ctr;
  logic [$clog2(WAIT_TICKS+1)-1:0] timeout;
  logic [31:0] cks;
  logic [31:0] ack_diff, loc_ack, stop, start;
  logic [RAM_DEPTH-1:0] space;
  logic [7:0] in_d_prev;
  logic connected, connected_prev, closed, closed_prev, load_pend;

  logic fifo_rst, load, upd;
  
  logic free, retrans;
  logic [$clog2(RETRANSMIT_TICKS+1)-1:0] timer;
  logic [7:0] tries;
  logic [PACKET_DEPTH:0] push_ptr, pop_ptr, info_space, flush_ctr;
  logic load_timeout, load_mtu, load_full, load_send;

  logic [RAM_DEPTH-1:0] buf_addr;
  length_t tx_byte_cnt, length;
  logic done;
  logic init;
  logic buf_rst;

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

    .write    (data.val && data.cts),
    .data_in  (data.dat),
    .space    (space),
    .addr     (buf_addr),
    .data_out (ctl.strm.dat),

    .seq (ctl.loc_seq),
    .ack (loc_ack),

    .f (full),
    .e (empty)
  );

  /////////////////////
  // Packet info RAM //
  /////////////////////
  ram_if_dp #(
    .AW (PACKET_DEPTH),
    .DW ($bits(tcp_pkt_t))
  ) data_ram (.*);

  ram_dp #(
    .AW (PACKET_DEPTH),
    .DW ($bits(tcp_pkt_t))
  ) data_ram_inst (data_ram);

  assign data_ram.clk_a = clk;
  assign data_ram.clk_b = clk;
  assign data_ram.rst   = rst;
  assign data_ram.a_a   = push_ptr[PACKET_DEPTH-1:0];
  assign data_ram.a_b   = upd_addr;
  assign data_ram.d_a   = new_pkt;
  assign data_ram.d_b   = upd_pkt;
  assign data_ram.w_a   = load;
  assign data_ram.w_b   = upd;
  assign new_pkt_q      = data_ram.q_a;
  assign upd_pkt_q      = data_ram.q_b;

  // Difference between push and pop ptr indicate the number of
  // individual packets that may be stored in packet info RAM
  assign info_space = push_ptr - pop_ptr + 1; // Add +1 to get correct full flag (no overwriting when full)

  // clear to send flag is generated from AND of:
  // 1. connected flag
  // 2. packet info RAM isn't full
  // 3. transmission data buffer isn't full 
  assign data.cts = (ctl.status == tcp_connected) && !info_space[PACKET_DEPTH] && !full;

  // New data for transmission didn't arrive for WAIT_TICKS
  assign load_timeout = (timeout == WAIT_TICKS && !data.val);
  // Packet length reached MTU
  assign load_mtu = (ctr == MTU - 80); // 60 for tcp header (with options) and another 20 for ipv4. todo: check for correctness
  // Transmission data buffer is full
  assign load_full = full;
  // Force sending a packet without waiting for WAIT_TICKS
  assign load_send = data.snd;

  assign load_pend = (w_fsm == w_pend_s) && (load_timeout || load_mtu || load_full || load_send);   
  assign new_pkt.length  = ctr; // length equals byte count for current packet. together with ctl.pld_info.seq logic reads out packet from ram
  assign new_pkt.cks     = ctr[0] ? cks + {in_d_prev, 8'h00} : cks;
  assign new_pkt.present = 1; // Every new entry in packet info table is ofc valid
  assign new_pkt.tries   = 0; // The packet hasn't been transmittd yet
  assign new_pkt.sacked  = 0; // create an unSACKed packet
  assign new_pkt.timer   = RETRANSMIT_TICKS; // preload so packet is read out asap the first time
  assign new_pkt.stop    = ctl.loc_seq; // equals expected ack for packet

  // Sequence number tracker
  always_ff @ (posedge clk) begin
    if (ctl.rst) ctl.loc_seq <= 0;
    else begin
      if (ctl.init) ctl.loc_seq <= ctl.tcb.loc_seq; // initialize current seq at connection reset;
      else if (data.cts && data.val) ctl.loc_seq <= ctl.loc_seq + 1;
    end
  end

  tcp_num_t prev_loc_seq;

  // Packet creation FSM
  always_ff @ (posedge clk) begin
    if (ctl.rst) begin
      ctr      <= 0;
      push_ptr <= 0;
      load     <= 0;
      timeout  <= 0;
      w_fsm    <= w_idle_s;
      init     <= 0;
    end
    else begin
      if (data.val) in_d_prev <= data.dat;
      case (w_fsm)
        w_idle_s : begin
          if (data.val && data.cts) begin
            ctr  <= 1;
            w_fsm <= w_pend_s;
          end
          prev_loc_seq <= ctl.loc_seq; // equals packet's seq
           // Can't add packet with zero length
          load <= 0;
          cks  <= 0;
          timeout <= 0;
        end
        w_pend_s : begin
          new_pkt.start <= prev_loc_seq;
          if (data.val && data.cts) begin
            ctr <= ctr + 1;
            cks <= (ctr[0]) ? cks + {in_d_prev, data.dat} : cks;
          end
          timeout <= (data.val) ? 0 : timeout + 1; // reset timeout if new byte arrives
          // either of three conditions to load new pakcet
          if (load_full || load_timeout || load_mtu || load_send) w_fsm <= w_idle_s;
        end
      endcase
      load <= (load_pend && !ctl.flush); // load packet 1 tick after 'load_pend'
      if (load) push_ptr <= push_ptr + 1;
    end
  end

  // remote host may acknowledge some part of the packet (mainly when sending payload of length > remote host window)
  // ctl RAM frees space based on ack_num
  // have to check if received ack_num acknowledges whole packet, otherwise ctl.data may be overwritten and checksum will be incorrect
  // pass packet's expected ack instead of remote ack
  // this is needed to avoid repacketisation
  
  // - free space         p s      r a          p a
  // = valid data         k e      e c          k c
  // x overwritten data   t q      m k          t k
  //                   ----|=====================|---- 
  //                   ----|========|xxxxxxxxxxxx|---- data loss if remote ack is passed directly to ctl RAM
  logic [31:0] diff_seq; 
  logic upd_last_seq;

  always_ff @ (posedge clk) diff_seq = stop - ctl.last_seq; // diff [31] means overflow
  assign upd_last_seq = (diff_seq[31] && (stop < ctl.last_seq)) || (!diff_seq[31] && (stop > ctl.last_seq));
  always_ff @ (posedge clk) begin
    if (ctl.rst) begin // Engine has to close connection to reenable ctl
      fsm              <= buf_idle_s;
      upd              <= 0;
      upd_addr         <= 0;
      ctl.force_dcn    <= 0;
      ctl.flushed      <= 0;
      ctl.send         <= 0;
      ctl.strm.val     <= 0;
      ctl.strm.sof     <= 0;
      ctl.strm.eof     <= 0;
      ctl.pld_info.seq <= 0;
      ctl.pld_info.lng <= 0;
      ctl.pld_info.cks <= 0;
      pop_ptr          <= 0;
      flush_ctr        <= 0;
      upd_pkt          <= 0;
  	  loc_ack          <= 0;
      ctl.last_seq     <= 0;
      tries            <= 0;
      timer            <= 0;
      free             <= 0;
      retrans          <= 0;
      start            <= 0;
      stop             <= 0;
      ack_diff         <= 0;
      tx_byte_cnt      <= 0;
      done             <= 0;
      length           <= 0;
      buf_addr         <= 0;
    end
    else begin
      // don't change these fields:
      upd_pkt.cks    <= upd_pkt_q.cks;
      upd_pkt.start  <= upd_pkt_q.start;
      upd_pkt.stop   <= upd_pkt_q.stop;
      upd_pkt.length <= upd_pkt_q.length;
      upd_addr_prev  <= upd_addr;
      case (fsm)
        buf_idle_s : begin
          if (ctl.init) begin
            loc_ack      <= ctl.tcb.rem_ack;
            ctl.last_seq <= ctl.tcb.loc_seq;
            fsm <= buf_scan_s;
          end
        end
        buf_scan_s : begin
          tx_byte_cnt <= 0;
          done        <= 0;
          upd         <= 0;
          ctl.flushed <= 0;
          // Continiously scan for unacked packets. If present flag found, check if it's acked (buf_check_s)
          // if packet at current address is not present, read next one and so on
          if (ctl.flush) fsm <= buf_flush_s; // ctl flush request during connection closure
          else if (ctl.tcb.wnd_scl >= MTU) begin
            if (upd_pkt_q.present) begin // if a packet is present (not yet acknowledged and stored in RAM)
              fsm      <= buf_choice_s; // read its pointers and length
              upd_addr <= upd_addr_prev;
              ack_diff <= upd_pkt_q.stop - ctl.tcb.rem_ack; // ack_diff[31] means either ack or expected ack ovfl
              timer    <= upd_pkt_q.timer;
              tries    <= upd_pkt_q.tries;
              start    <= upd_pkt_q.start;
              stop     <= upd_pkt_q.stop;
              length   <= upd_pkt_q.length;
              free     <= 0;
              retrans  <= 0;
              ctl.pld_info.seq  <= upd_pkt_q.start;
  	          ctl.pld_info.lng  <= upd_pkt_q.length;
         	    ctl.pld_info.cks  <= upd_pkt_q.cks;
            end
            else upd_addr <= upd_addr + 1;
          end
        end
        buf_choice_s : begin
          fsm <= buf_check_s;
          if (ack_diff[31] || ack_diff == 0) free <= 1; // free packet if stop (expected ack) is less than remote ack
  		    else if (!ack_diff[31] && (timer == RETRANSMIT_TICKS)) retrans <= 1; // only transmit if previous packets were sent at least once, and packet is not acked
        end
        buf_check_s : begin
          if (!load && !load_pend) begin // if TX path isn't busy (e.g. pure ACK) and RAM isn't being loaded with new packet...
            upd <= 1;
            if (free) begin // clear present flag if acked
              fsm <= buf_next_s;
              upd_pkt.present <= 0;
              upd_pkt.timer   <= 0;
              upd_pkt.tries   <= 0;
              ctl.send        <= 0;
            end
            else if (retrans) begin
              fsm <= buf_retrans_s;
              buf_addr <= ctl.pld_info.seq;//[RAM_DEPTH-1:0];
              if (tries == RETRANSMIT_TRIES) ctl.force_dcn <= 1;
              upd_pkt.present <= 1;
              upd_pkt.timer   <= 0;
              upd_pkt.tries   <= tries + 1;
              ctl.send        <= 1;
            end
            else begin
              fsm <= buf_next_s;
              upd_pkt.present <= 1;
              upd_pkt.tries   <= tries; // increment retransmit timer
              ctl.send        <= 0;
              if (timer != RETRANSMIT_TICKS) upd_pkt.timer <= timer + 1; // prevent overctl
            end
          end
        end
        buf_next_s : begin
          if (free) begin
            pop_ptr <= pop_ptr + 1;
            loc_ack <= stop;
          end
          upd           <= 0;
          upd_addr_prev <= upd_addr + 1;
          upd_addr      <= upd_addr + 1;
          fsm           <= buf_wait_s;
        end
        buf_wait_s : begin
          fsm <= buf_scan_s;
        end
        buf_retrans_s : begin
          upd <= 0;
          if (ctl.req) begin
            ctl.strm.val <= !done;
            ctl.strm.sof <= (tx_byte_cnt == 0);
            ctl.strm.eof <= (tx_byte_cnt == ctl.pld_info.lng - 1);
            if (tx_byte_cnt == ctl.pld_info.lng - 1) done <= 1;
            tx_byte_cnt <= tx_byte_cnt + 1;
            buf_addr <= buf_addr + 1;
            ctl.send <= 0;
          end
          if (ctl.flush) fsm <= buf_flush_s; // Abort retransmission // todo: rework disconnect reset logic
          else if (ctl.sent) begin // Wait for done signal. Can't use !busy due to unkown tx output delay
            if (upd_last_seq) ctl.last_seq <= stop; // Update last seq that was actually sent
            fsm          <= buf_scan_s;
            upd_addr     <= upd_addr + 1;
          end
        end
        buf_flush_s : begin
          ctl.send        <= 0;
          upd_addr        <= upd_addr + 1;
          upd_pkt.present <= 0;
          upd             <= 1;
          flush_ctr <= flush_ctr + 1;
          if (flush_ctr == 0 && upd) begin
            ctl.flushed <= 1;
          end
        end
        default : begin
          upd             <= 0;
          ctl.force_dcn   <= 1;
          ctl.send        <= 0;
          upd_pkt.present <= 0;
          upd_pkt.timer   <= 0;
          upd_pkt.tries   <= 0;
          fsm             <= buf_scan_s;
        end
      endcase
    end
  end

endmodule : tcp_vlg_tx_ctl
