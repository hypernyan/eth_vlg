import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_rx_ctrl #(
  parameter int MTU              = 1500, // Maximum pld length
  parameter int RETRANSMIT_TICKS = 1000000,
  parameter int RETRANSMIT_TRIES = 5,
  parameter int RAM_DEPTH        = 10,
  parameter int PACKET_DEPTH     = 3,
  parameter int WAIT_TICKS       = 20,
  parameter int ACK_TIMEOUT      = 20

)
(
  input    logic  clk,
  input    logic  rst,
  input    dev_t  dev,
  tcp.in_rx       rx,
  rx_ctrl.in      ctrl,
  tcp_data.out_rx data // user inteface (raw TCP stream)
);

  logic port_flt, ack_rec, fsm_rst;
  tcp_num_t loc_ack;
  logic receiving;

  assign port_flt = rx.meta.val && (rx.meta.tcp_hdr.src_port == ctrl.tcb.rem_port) && (rx.meta.tcp_hdr.dst_port == ctrl.tcb.loc_port);
  assign ack_rec = port_flt && rx.meta.tcp_hdr.tcp_flags.ack && (rx.meta.tcp_hdr.tcp_seq_num == loc_ack);
  always @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= ctrl.flush;

  /////////////////////////////
  // Acknowledgement control //
  /////////////////////////////

  tcp_vlg_ack #(
    .TIMEOUT (ACK_TIMEOUT)
  )
  tcp_vlg_ack_inst (
    .clk       (clk),
    .rst       (rst),
    .rx        (rx),
    .tcb       (ctrl.tcb), // initialize with ack that was negotiated
    .init      (ctrl.init), // 1-tick long initialisation signal
    .loc_ack   (loc_ack), // current local ack
    .connected (ctrl.connected),
    .send      (ctrl.send_ack),
    .sent      (ctrl.ack_sent)
  );

  logic val;
  logic err;
  logic eof;
  logic [7:0] dat;

  always @ (posedge clk) begin
    if (rst) begin
    //  data.val  <= 0;
    //  data.dat  <= 0;
    //  data.err  <= 0;
      receiving <= 0;
      ctrl.loc_ack <= 0;
    end
    else begin
      val <= rx.strm.val;
      dat <= rx.strm.dat;
      err <= rx.strm.err;
      eof <= rx.strm.err;
      ctrl.loc_ack <= loc_ack;
      if (ctrl.connected && ack_rec && rx.meta.pld_len != 0) receiving <= 1;
      else if (eof) receiving <= 0;
    end
  end

  assign data.val = (receiving) ? val : 0;
  assign data.dat = (receiving) ? dat : 0;
  assign data.err = (receiving) ? err : 0;

endmodule : tcp_vlg_rx_ctrl
