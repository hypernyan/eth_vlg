// Acknowledgement packet generation is sourced from this logic:
// There are several events that trigger pure acks:
// - 
//
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
  input  tcb_t      tcb,
  input  logic      init,
  input  tcp_num_t  loc_ack, // send pure ack upon ack timeout or exceeding unacked received packets count 
  input  logic      sack_upd, // sack update will trigger forced ack
  input  tcp_stat_t status,
  output logic      send,    // send pure ack upon ack timeout or exceeding unacked received packets count 
  input  logic      sent     // tx logic will confirm as soon as packet is sent
);

  logic [$clog2(TIMEOUT+1)-1:0] timer;

  logic [$clog2(FORCE_ACK_PACKETS+1)-1:0] unacked_pkts;
  logic acked; // data is acked, no need to do anything

  logic timeout_ack, pkts_ack;

  // means packet with local ack was actually sent (ack indeed reported)
  // if 'acked', avoid sending pure acks as last ack was already reported 
  always_ff @ (posedge clk) acked <= (loc_ack == tcb.loc_ack);

  /////////////////////////////
  // Unacked packets tracker //
  /////// for forced ack //////
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
      end 
    end
  end

  assign timeout_ack = (timer == TIMEOUT - 1); // Ack due to timeout

  /////////////
  // Ack mux //
  /////////////

  always_ff @ (posedge clk) begin
    // reset send flag after packet was sent, but don't hold it to '1'
    if (rst) send <= 0; else if (timeout_ack || pkts_ack || sack_upd) send <= 1; else if (sent) send <= 0;
  end

  always_ff @ (posedge clk) begin
  //  if (VERBOSE && !send) if (timeout_ack) $display("Force ack due to timeout");
  //  if (VERBOSE && !send) if (pkts_ack) $display("Force ack due to packet count");
  end

endmodule : tcp_vlg_ack
