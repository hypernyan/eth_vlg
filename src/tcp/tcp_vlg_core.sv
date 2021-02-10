import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_core #(
  parameter int MTU                = 1500,
  parameter int RETRANSMIT_TICKS   = 1000000,
  parameter int RETRANSMIT_TRIES   = 5,
  parameter int RAM_DEPTH          = 12,
  parameter int PACKET_DEPTH       = 8,
  parameter int WAIT_TICKS         = 100,
  parameter int CONNECTION_TIMEOUT = 10000000,
  parameter int ACK_TIMEOUT        = 125000,
  parameter int KEEPALIVE_PERIOD   = 600000000,
  parameter int KEEPALIVE_INTERVAL = 125000000,
  parameter bit ENABLE_KEEPALIVE   = 1,
  parameter int KEEPALIVE_TRIES    = 5,
  parameter bit VERBOSE            = 0
)
(
  input logic clk,
  input logic rst,

  input dev_t     dev,
  tcp.in_rx       rx,
  tcp.out_tx      tx,
  tcp_data.in_tx  in,
  tcp_data.out_rx out,
  tcp_ctl.in     ctl
);

tcp tcp_tx_fsm(.*);
tcp tcp_tx_buf(.*);
tcp tcp_rx(.*);
rx_ctl rx_ctl(.*);
tx_ctl tx_ctl(.*);

///////////////////////
// TCP state machine //
///////////////////////
tcp_vlg_engine #(
  .MTU                (MTU),
  .CONNECTION_TIMEOUT (CONNECTION_TIMEOUT),
  .ACK_TIMEOUT        (ACK_TIMEOUT),
  .KEEPALIVE_PERIOD   (KEEPALIVE_PERIOD),
  .KEEPALIVE_INTERVAL (KEEPALIVE_INTERVAL),
  .ENABLE_KEEPALIVE   (ENABLE_KEEPALIVE),
  .KEEPALIVE_TRIES    (KEEPALIVE_TRIES),
  .VERBOSE            (VERBOSE)
) tcp_vlg_engine_inst (
  .clk      (clk),
  .rst      (rst),
  .dev      (dev),
  .rx       (rx),
  .tx       (tx),
  .rx_ctl  (rx_ctl),
  .tx_ctl  (tx_ctl),
  .ctl     (ctl)
);
////////////////////////////////
// Receive buffer and control //
////////////////////////////////
tcp_vlg_rx_ctl #(
  .MTU              (MTU),
  .RETRANSMIT_TICKS (RETRANSMIT_TICKS),
  .RETRANSMIT_TRIES (RETRANSMIT_TRIES),
  .RAM_DEPTH        (RAM_DEPTH),
  .PACKET_DEPTH     (PACKET_DEPTH),
  .WAIT_TICKS       (WAIT_TICKS),
  .ACK_TIMEOUT      (ACK_TIMEOUT)
) tcp_vlg_rx_ctl_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .rx   (rx),
  .data (out),
  .ctl (rx_ctl)
);
/////////////////////////////////////
// Transmission buffer and control //
/////////////////////////////////////
tcp_vlg_tx_ctl #(
  .MTU              (MTU),
  .RETRANSMIT_TICKS (RETRANSMIT_TICKS),
  .RETRANSMIT_TRIES (RETRANSMIT_TRIES),
  .RAM_DEPTH        (RAM_DEPTH),
  .PACKET_DEPTH     (PACKET_DEPTH),
  .WAIT_TICKS       (WAIT_TICKS)
) tcp_vlg_tx_ctl_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .data (in),
  .ctl (tx_ctl)
);

endmodule : tcp_vlg_core
