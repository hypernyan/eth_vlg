module tcp_vlg_rx_ctl
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
 #(
  parameter int    ACK_TIMEOUT       = 20,
  parameter int    FORCE_ACK_PACKETS = 5,
  parameter bit    VERBOSE           = 0,
  parameter string DUT_STRING        = ""
)
(
  input    logic  clk,
  input    logic  rst,
  input    dev_t  dev,
  tcp.in_rx       rx,
  rx_ctl.in       ctl,
  tcp_data.out_rx data // user inteface (raw TCP stream)
);

  logic port_flt, ack_rec, fsm_rst;
  tcp_num_t loc_ack;
  logic receiving;
  logic eof;

  assign port_flt = rx.meta.val && (rx.meta.tcp_hdr.src_port == ctl.tcb.rem_port) && (rx.meta.tcp_hdr.dst_port == ctl.tcb.loc_port);
  assign ack_rec = port_flt && rx.meta.tcp_hdr.tcp_flags.ack && (rx.meta.tcp_hdr.tcp_seq_num == loc_ack);
  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= ctl.flush;

  /////////////////////////////
  // Acknowledgement control //
  /////////////////////////////

  tcp_vlg_ack #(
    .TIMEOUT           (ACK_TIMEOUT),
    .FORCE_ACK_PACKETS (FORCE_ACK_PACKETS),
    .VERBOSE           (VERBOSE),
    .DUT_STRING        (DUT_STRING)
  )
  tcp_vlg_ack_inst (
    .clk       (clk),
    .rst       (rst),
    .rx        (rx),
    .tcb       (ctl.tcb),  // initialize with ack that was negotiated
    .init      (ctl.init), // 1-tick long initialisation signal
    .loc_ack   (loc_ack),  // current local ack
    .status    (ctl.status),
    .send      (ctl.send_ack),
    .sent      (ctl.ack_sent)
  );

  logic val;
  logic err;
  logic [7:0] dat;

  always_ff @ (posedge clk) begin
    if (rst) begin
      val <= 0;
      dat <= 0;
      err <= 0;
      eof <= 0;
      receiving <= 0;
      ctl.loc_ack <= 0;
    end
    else begin
      val <= rx.strm.val;
      dat <= rx.strm.dat;
      err <= rx.strm.err;
      eof <= rx.strm.eof;
      data.val <= (receiving) ? val : 0;
      data.dat <= (receiving) ? dat : 0;
      data.err <= (receiving) ? err : 0;
      ctl.loc_ack <= loc_ack;
      if ((ctl.status == tcp_connected) && ack_rec && rx.meta.pld_len != 0) receiving <= 1;
      else if (eof) receiving <= 0;
    end
  end

endmodule : tcp_vlg_rx_ctl
