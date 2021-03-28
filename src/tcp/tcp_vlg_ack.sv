// Acknowledgement control:
// Keeps track of local acknowledgement number
// loc ack is always valid after init goes low
// loc_ack in TCB is updated upon sending a packet with that ack in engine logic

// The logic here consists of two parts:

module tcp_vlg_ack
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int    TIMEOUT           = 1250,
  parameter int    FORCE_ACK_PACKETS = 5, // Force ack w/o timeout if this amount of packets was received
  parameter bit    VERBOSE           = 0,
  parameter string DUT_STRING        = ""
)
(
  input  logic      clk,
  input  logic      rst,
  tcp.in_rx         rx,
  input  tcp_stat_t status,

  input  tcb_t      tcb,  // contains initial loc_ack or 
  input  logic      init, // initializa local ack with value from TCB 
 
  output tcp_num_t  loc_ack, // current local acknowledgement number
 
  output logic      send, // send pure ack upon ack timeout or exceeding unacked received packets count 
  input  logic      sent  // tx logic will confirm as soon as packet is sent
);

  logic [31:0] diff;

  logic [$clog2(TIMEOUT+1)-1:0] timer;

  logic [$clog2(FORCE_ACK_PACKETS+1)-1:0] unacked_pkts;
  logic acked; // data is acked, no need to do anything

  tcp_num_t rem_seq;
  logic timeout_ack;
  logic pkts_ack;
  logic upd_loc_ack;
  logic loc_ack_updated;

  assign diff = rem_seq - loc_ack;
  // update local ack only when remote sequence of incoming packet is greater then current value
  // this is to prevent local ack updates on old sequence number from out of order packets
  // account for overflow around ffffffff with diff[31]
  assign upd_loc_ack = (diff[31] && (rem_seq < loc_ack)) || (!diff[31] && (rem_seq > loc_ack));

  always_ff @ (posedge clk) begin
    if (rst) begin
      loc_ack <= 0;
      acked   <= 0;
      rem_seq <= 0;
      loc_ack_updated <= 0;
    end
    else begin
      // initializa local ack during TWHS
      if (init) loc_ack <= tcb.loc_ack;
      else if (rx.meta.val) begin
        loc_ack_updated <= 1;
        // update remote sequence from incoming packets.
        rem_seq <= rx.meta.tcp_hdr.tcp_seq_num + rx.meta.pld_len;
        // If current reported rem_seq is higher than local ack, update local ack
        if (upd_loc_ack && !loc_ack_updated) loc_ack <= rx.meta.tcp_hdr.tcp_seq_num + rx.meta.pld_len;
      end
      else loc_ack_updated <= 0;
      if (status == tcp_connected) begin // todo: rm else?
        acked <= (loc_ack == tcb.loc_ack);
      end
    end
  end

  /////////////////////////////
  // Unacked packets tracker //
  /////////////////////////////
 
  always_ff @ (posedge clk) begin
    if (rst) begin
      unacked_pkts <= 0;
    end
    else begin
      if (acked) unacked_pkts <= 0;
      else begin
        if (send) unacked_pkts <= 0; // reset unacked packet counter as Ack was just sent.
        // If maximum amount of unacked packets was reached, stop counting. Indicating focre ack condition
        else if (rx.strm.sof) unacked_pkts <= pkts_ack ? unacked_pkts : unacked_pkts + 1;
      end
    end
  end
  assign pkts_ack = (unacked_pkts == FORCE_ACK_PACKETS); // Ack due to unacked packet count

  ///////////////
  // Ack timer //
  ///////////////

  always_ff @ (posedge clk) begin
    if (rst) begin
      timer <= 0;
    end
    else begin
      if (status == tcp_connected) begin
        // keep timer reset if acked
        // or reset timer after receiving unacked packet
        if (acked || (rx.meta.val && (rx.meta.tcp_hdr.tcp_seq_num + rx.meta.pld_len) != loc_ack)) timer <= 0;
        // keep timer at TIMEOUT until 
        else timer <= (timer == TIMEOUT) ? TIMEOUT : timer + 1;
        // Reset send flag after packet was sent, but don't hold it to '1'
      end 
    end
  end
  assign timeout_ack = (timer == TIMEOUT - 1);              // Ack due to timeout

  /////////////
  // Ack mux //
  /////////////

  always_ff @ (posedge clk) begin
    if (rst) send <= 0; else if (timeout_ack || pkts_ack) send <= 1; else if (sent) send <= 0;
  end

  always_ff @ (posedge clk) begin
    if (VERBOSE && !send) if (timeout_ack) $display("Force ack due to timeout");
    if (VERBOSE && !send) if (pkts_ack) $display("Force ack due to packet count");
  end

endmodule : tcp_vlg_ack