// see rfc3517 p.2 duplicate duplicate acknowledgments
module tcp_vlg_fast_rtx
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  // Fast retransmit a segment if this amount of dup acks received
  // Or SACK blocks are detected
  parameter int    DUP_ACKS   = 3,
  parameter bit    VERBOSE    = 0,
  parameter string DUT_STRING = ""
)
(
  input logic clk,
  input logic rst,
  input tcb_t tcb,
  input tcp_stat_t status,

  tcp.in_rx rx,

  output logic     dup_det, // duplicate acknowledge detected
  output tcp_num_t dup_ack  // last detected ack
);

  logic [$clog2(DUP_ACKS+1)-1:0] dup_ack_ctr;
  logic fsm_rst;
  logic last_ack_updated;

  // keep logic off
  // if local seq is equal to remote ack
  // meaning that all data is acked
  always_ff @ (posedge clk) fsm_rst  <= (tcb.loc_seq == tcb.rem_ack) || rst;
  always_ff @ (posedge clk) dup_det <= (dup_ack_ctr == DUP_ACKS);

  //////////////
  // Dup acks //
  //////////////

  // Fast retransmit a packet that contains dup_ack
  // As the segment just after dup_ack is probably lost
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      dup_ack_ctr <= 0;
      last_ack_updated <= 0;
    end
    else begin
      if (status == tcp_connected && rx.meta.val && rx.meta.tcp_hdr.tcp_flags.ack) begin // Receiving an ACK packet
        last_ack_updated <= 1; // increment dup_ack_ctr.
        if (!last_ack_updated) begin // deassert after 1 tick
          dup_ack <= rx.meta.tcp_hdr.tcp_ack_num;
          if (dup_ack == rx.meta.tcp_hdr.tcp_ack_num) dup_ack_ctr <= (dup_ack_ctr == DUP_ACKS) ? dup_ack_ctr : dup_ack_ctr + 1;
          else dup_ack_ctr <= 0;
        end
      end
      else last_ack_updated <= 0;
    end
  end

endmodule : tcp_vlg_fast_rtx
