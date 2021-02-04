import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_tx_ctrl #(
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
  tx_ctrl.in     ctrl  // tx buffer control
);

  enum logic {w_idle_s, w_pend_s} w_fsm;
  
  enum logic [6:0] {
    buf_scan_s,
    buf_check_s,
    buf_choice_s,
    buf_next_s,
    buf_wait_s,
    buf_retrans_s,
    buf_flush_s
  } fsm;

  tcp_pkt_t upd_pkt, upd_pkt_q, new_pkt, new_pkt_q;

  logic [PACKET_DEPTH-1:0] new_addr, upd_addr, upd_addr_prev;
  logic [$clog2(MTU+1)-1:0] ctr;
  logic [$clog2(WAIT_TICKS+1)-1:0] timeout;
  logic [31:0] cks;
  logic [31:0] ack_diff, loc_ack, stop, start;
  logic [RAM_DEPTH-1:0] space;
  logic [7:0] in_d_prev;
  logic connected_prev, load_pend;

  logic fifo_rst, load, upd, cks_rst;
  
  logic free, retrans;
  logic [$clog2(RETRANSMIT_TICKS+1)-1:0] timer;
  logic [7:0] tries;
  logic [PACKET_DEPTH:0] push_ptr, new_ptr_ahead, pop_ptr, diff, flush_ctr;
  logic load_timeout, load_mtu, load_full, load_send;

  logic [RAM_DEPTH-1:0] buf_addr;
  logic buf_rst;
  length_t tx_byte_cnt, length;
  logic done;

  //////////////////////////////
  // Transmission data buffer //
  //////////////////////////////
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
    .data_out (ctrl.strm.dat),

    .seq (ctrl.loc_seq),
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
  assign diff = push_ptr - pop_ptr + 1; // Add +1 to get correct full flag (no overwriting when full)

  // clear to send flag is generated from AND of:
  // 1. connected flag
  // 2. packet info RAM isn't full
  // 3. transmission data buffer isn't full 
  assign data.cts = ctrl.connected && !diff[PACKET_DEPTH] && !full;
  // assign new_addr[PACKET_DEPTH-1:0] = push_ptr[PACKET_DEPTH-1:0];

  // Reset 
  always @ (posedge clk) connected_prev <= ctrl.connected; 
  always @ (posedge clk) if (rst) fifo_rst <= 1; else fifo_rst <= (connected_prev != ctrl.connected);
  always @ (posedge clk) if (rst) buf_rst <= 1; else buf_rst <= fifo_rst;

  // New data for transmission didn't arrive for WAIT_TICKS ticks
  assign load_timeout = (timeout == WAIT_TICKS && !data.val);
  // Packet length reached MTU
  assign load_mtu = (ctr == MTU - 80); // 60 for tcp header (with options) and another 20 for ipv4. todo: check for correctness
  // Transmission data buffer is full
  assign load_full = full;
  // Force sending a packet without waiting for WAIT_TICKS
  assign load_send = data.snd;

  assign load_pend = (w_fsm == w_pend_s) && (load_timeout || load_mtu || load_full || load_send);   
  assign new_pkt.length  = ctr; // length equals byte count for current packet. together with ctrl.seq logic reads out packet from ram
  assign new_pkt.cks     = ctr[0] ? cks + {in_d_prev, 8'h00} : cks;
  assign new_pkt.present = 1; // this packet is pending in memory
  assign new_pkt.tries   = 0; // haven't tried to transmit the packet
  assign new_pkt.sacked  = 0; // create an unSACKed packet
  assign new_pkt.timer   = RETRANSMIT_TICKS; // preload so packet is read out asap the first time
  assign new_pkt.stop    = ctrl.loc_seq; // equals expected ack for packet

  // Sequence number tracker
  always @ (posedge clk) begin
    if (rst) ctrl.loc_seq <= 0;
    else begin
      if (ctrl.init) ctrl.loc_seq <= ctrl.tcb.loc_seq; // initialize current seq at connection reset;
      if (data.cts && data.val) ctrl.loc_seq <= ctrl.loc_seq + 1;
    end
  end
  
  tcp_num_t prev_loc_seq;

  // Packet creation FSM
  always @ (posedge clk) begin
    if (fifo_rst || ctrl.flush) begin
      ctr      <= 0;
      push_ptr <= 0;
      load     <= 0;
      timeout  <= 0;
      w_fsm    <= w_idle_s;
    end
    else begin
      if (data.val) in_d_prev <= data.dat;
      case (w_fsm)
        w_idle_s : begin
          if (data.val && data.cts) begin
            ctr  <= 1;
            w_fsm <= w_pend_s;
          end
          prev_loc_seq <= ctrl.loc_seq; // equals packet's seq
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
      load <= load_pend; // load packet 1 tick after 'load_pend'
      if (load) push_ptr <= push_ptr + 1;
    end
  end

  // remote host may acknowledge some part of the packet (mainly when sending ctrl.data of length > remote host window)
  // ctrl RAM frees space based on ack_num
  // have to check if received ack_num acknowledges whole packet, otherwise ctrl.data may be overwritten and checksum will be incorrect
  // pass packet's expected ack instead of remote ack
  // this is needed to avoid repacketisation
  
  // - free space               p s      r a          p a
  // = valid ctrl.data          k e      e c          k c
  // x overwritten ctrl.data    t q      m k          t k
  // -----------------------------|========|============|-------- 
  // -----------------------------|========|xxxxxxxxxxxx|-------- ctrl.data loss if remote ack is passed directly to ctrl RAM

  always @ (posedge clk) begin
    if (fifo_rst) begin // Engine has to close connection to reenable ctrl
      fsm            <= buf_scan_s;
      upd            <= 0;
      upd_addr       <= 0;
      ctrl.force_dcn <= 0;
      ctrl.flushed   <= 0;
      ctrl.send      <= 0;
      ctrl.strm.val  <= 0;
      ctrl.strm.sof  <= 0;
      ctrl.strm.eof  <= 0;
      ctrl.pkt_seq   <= 0;
      ctrl.len       <= 0;
      ctrl.cks       <= 0;
      pop_ptr        <= 0;
      flush_ctr      <= 0;
      upd_pkt        <= 0;
  	  loc_ack        <= ctrl.tcb.rem_ack;
      tries          <= 0;
      timer          <= 0;
      free           <= 0;
      retrans        <= 0;
      start          <= 0;
      stop           <= 0;
      ack_diff       <= 0;
      tx_byte_cnt    <= 0;
      done           <= 0;
    end
    else begin
      // don't change these fields:
      upd_pkt.cks    <= upd_pkt_q.cks;
      upd_pkt.start  <= upd_pkt_q.start;
      upd_pkt.stop   <= upd_pkt_q.stop;
      upd_pkt.length <= upd_pkt_q.length;
      upd_addr_prev  <= upd_addr;
      case (fsm)
        buf_scan_s : begin
          tx_byte_cnt  <= 0;
          done         <= 0;
          upd          <= 0;
          ctrl.flushed <= 0;
          // Continiously scan for unacked packets. If present flag found, check if it's acked (buf_check_s)
          // if packet at current address is not present, read next one and so on
          if (ctrl.flush) fsm <= buf_flush_s; // ctrl flush request during connection closure
          else if (upd_pkt_q.present) begin // if a packet is present (not yet acknowledged and stored in RAM)
            fsm      <= buf_choice_s; // read its pointers and length
            upd_addr <= upd_addr_prev;
            ack_diff <= upd_pkt_q.stop - ctrl.tcb.rem_ack; // ack_diff[31] means either ack or expected ack ovfl
            timer    <= upd_pkt_q.timer;
            tries    <= upd_pkt_q.tries;
            start    <= upd_pkt_q.start;
            stop     <= upd_pkt_q.stop;
            length   <= upd_pkt_q.length;
            free     <= 0;
            retrans  <= 0;
            ctrl.pkt_seq <= upd_pkt_q.start;
  	        ctrl.len     <= upd_pkt_q.length;
         	  ctrl.cks     <= upd_pkt_q.cks;
          end
          else upd_addr <= upd_addr + 1;
        end
        buf_choice_s : begin
          fsm <= buf_check_s;
          if (ack_diff[31] || ack_diff == 0) free <= 1; // free packet if stop (expected ack) is less than remote ack
  		    else if (!ack_diff[31] && (timer == RETRANSMIT_TICKS) && (ctrl.tcb.win_scl >= MTU)) retrans <= 1; // only transmit if previous packets were sent at least once, and packet is not acked
        end
        buf_check_s : begin
          if (!load && !load_pend) begin // if TX path isn't busy (e.g. pure ACK) and RAM isn't being loaded with new packet...
            upd <= 1;
            if (free) begin // clear present flag if acked
              fsm <= buf_next_s;
              upd_pkt.present <= 0;
              upd_pkt.timer   <= 0;
              upd_pkt.tries   <= 0;
              ctrl.send       <= 0;
            end
            else if (retrans) begin
              fsm <= buf_retrans_s;
              buf_addr <= ctrl.pkt_seq;//[RAM_DEPTH-1:0];
              if (tries == RETRANSMIT_TRIES) ctrl.force_dcn <= 1;
              upd_pkt.present <= 1;
              upd_pkt.timer   <= 0;
              upd_pkt.tries   <= tries + 1;
              ctrl.send       <= 1;
            end
            else begin
              fsm <= buf_next_s;
              upd_pkt.present <= 1;
              upd_pkt.tries   <= tries; // increment retransmit timer
              ctrl.send       <= 0;
              if (timer != RETRANSMIT_TICKS) upd_pkt.timer <= timer + 1; // prevent overctrl
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
//          last_start <= (last_start < start) ? start : last_start;
//          last_stop  <= (last_stop  < stop)  ? stop  : last_stop;
          if (ctrl.req) begin
            ctrl.strm.val <= !done;
            ctrl.strm.sof <= (tx_byte_cnt == 0);
            ctrl.strm.eof <= (tx_byte_cnt == ctrl.len - 1);
            if (tx_byte_cnt == ctrl.len - 1) done <= 1;
            tx_byte_cnt <= tx_byte_cnt + 1;
            buf_addr <= buf_addr + 1;
          end
          if (ctrl.sent) begin // Wait for done signal. Can't use !busy due to unkown tx output delay
            fsm       <= buf_scan_s;
            ctrl.send <= 0;
            upd_addr  <= upd_addr + 1;
          end
        end
        buf_flush_s : begin
          ctrl.send       <= 0;
          upd_addr        <= upd_addr + 1;
          upd_pkt.present <= 0;
          upd             <= 1;
          flush_ctr <= flush_ctr + 1;
          if (flush_ctr == 0 && upd) begin
            ctrl.flushed <= 1;
          end
        end
        default : begin
          upd             <= 0;
          ctrl.force_dcn  <= 1;
          ctrl.send       <= 0;
          upd_pkt.present <= 0;
          upd_pkt.timer   <= 0;
          upd_pkt.tries   <= 0;
          fsm             <= buf_scan_s;
        end
      endcase
    end
  end

endmodule : tcp_vlg_tx_ctrl
