module tcp_vlg
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int    MTU                   = 1500,
  parameter int    RETRANSMIT_TICKS      = 1000000,
  parameter int    SACK_RETRANSMIT_TICKS = 1000000,
  parameter int    FAST_RETRANSMIT_TICKS = 1000000,
  parameter int    RETRANSMIT_TRIES      = 5,
  parameter int    RX_RAM_DEPTH          = 12,
  parameter int    TX_RAM_DEPTH          = 12,
  parameter int    PACKET_DEPTH          = 8,
  parameter int    WAIT_TICKS            = 100,
  parameter int    CONNECTION_TIMEOUT    = 10000000,
  parameter int    ACK_TIMEOUT           = 125000,
  parameter int    FORCE_ACK_PACKETS     = 5,
  parameter int    DUP_ACKS              = 5,
  parameter int    KEEPALIVE_PERIOD      = 600000000,
  parameter int    KEEPALIVE_INTERVAL    = 600000000,
  parameter bit    ENABLE_KEEPALIVE      = 1,
  parameter int    KEEPALIVE_TRIES       = 5,
  parameter bit    VERBOSE               = 0,
  parameter string DUT_STRING            = ""
)
(
  input logic     clk,
  input logic     rst,
  input dev_t     dev,
  ipv4.in_rx      rx,
  ipv4.out_tx     tx,
  tcp_data.in_tx  in,
  tcp_data.out_rx out,
  tcp_ctl.in      ctl
);

  tcp tcp_tx(.*);
  tcp tcp_rx(.*);

  tcb_t tcb;

  tcp_vlg_rx tcp_vlg_rx_inst (  
    .clk  (clk),
    .rst  (rst),
    .ipv4 (rx),    // ipv4
    .tcp  (tcp_rx) // stripped from ipv4, raw tcp
  );

  tcp_vlg_core  #(
    .MTU                   (MTU),
    .RETRANSMIT_TICKS      (RETRANSMIT_TICKS),
    .SACK_RETRANSMIT_TICKS (SACK_RETRANSMIT_TICKS),
    .FAST_RETRANSMIT_TICKS (FAST_RETRANSMIT_TICKS),
    .RETRANSMIT_TRIES      (RETRANSMIT_TRIES),
    .RX_RAM_DEPTH          (RX_RAM_DEPTH),
    .TX_RAM_DEPTH          (TX_RAM_DEPTH),
    .PACKET_DEPTH          (PACKET_DEPTH),
    .WAIT_TICKS            (WAIT_TICKS),
    .CONNECTION_TIMEOUT    (CONNECTION_TIMEOUT),
    .ACK_TIMEOUT           (ACK_TIMEOUT),
    .FORCE_ACK_PACKETS     (FORCE_ACK_PACKETS),
    .DUP_ACKS              (DUP_ACKS),
    .KEEPALIVE_PERIOD      (KEEPALIVE_PERIOD),
    .KEEPALIVE_INTERVAL    (KEEPALIVE_INTERVAL),
    .ENABLE_KEEPALIVE      (ENABLE_KEEPALIVE),
    .KEEPALIVE_TRIES       (KEEPALIVE_TRIES),
    .VERBOSE               (VERBOSE),
    .DUT_STRING            (DUT_STRING)
  ) tcp_vlg_core_inst (
    .clk (clk),
    .rst (rst),
    .dev (dev),
    .rx  (tcp_rx),
    .tx  (tcp_tx),
    .in  (in),
    .out (out),
    .ctl (ctl)
  );

  tcp_vlg_tx #(
    .RAM_DEPTH (TX_RAM_DEPTH)
  ) tcp_vlg_tx_inst (
    .clk  (clk),
    .rst  (rst),
    .ipv4 (tx),
    .tcp  (tcp_tx)
  );

endmodule : tcp_vlg
