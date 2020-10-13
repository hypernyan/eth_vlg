
import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;
interface tcp;
  logic [7:0]   d;
  logic         v;
  logic         sof;
  logic         eof;
  logic         err;
  logic         rdy;
  logic         done;
  logic         busy;
  logic         req;
  tcp_hdr_t     tcp_hdr;
  tcp_opt_hdr_t tcp_opt_hdr;
  logic         tcp_hdr_v;
  ipv4_hdr_t    ipv4_hdr;
  mac_hdr_t     mac_hdr;
  length_t      payload_length;
  logic [31:0]  payload_chsum;
  
  modport in  (input  d, v, sof, eof, payload_length, payload_chsum, err, tcp_hdr, tcp_opt_hdr, tcp_hdr_v, ipv4_hdr, mac_hdr, rdy, output req, done, busy);
  modport out (output d, v, sof, eof, payload_length, payload_chsum, err, tcp_hdr, tcp_opt_hdr, tcp_hdr_v, ipv4_hdr, mac_hdr, rdy, input  req, done, busy);
endinterface

interface queue_if #(
  parameter int RAM_WIDTH = 8,
  parameter int RAM_DEPTH = 14
);
  logic                      pend;
  tcp_vlg_pkg::tcp_seq_num_t seq;
  eth_vlg_pkg::length_t      len;
  logic [31:0]               cs;
  logic                      flush; 
  logic                      flushed; 
  logic                      force_fin;  
  logic [RAM_WIDTH-1:0]      data;
  logic [RAM_DEPTH-1:0]      addr;

  modport out     (output pend, seq, len, cs, flushed, force_fin, input flush);
  modport in      (input pend, seq, len, cs, flushed, force_fin, output flush);
  modport out_ram (output data, input addr);
  modport in_ram  (input  data, output addr);
endinterface : queue_if

module tcp_vlg #(
  parameter MAX_PAYLOAD_LEN  = 1400,
  parameter RETRANSMIT_TICKS = 1000000,
  parameter RETRANSMIT_TRIES = 5,
  parameter RAM_DEPTH        = 12,
  parameter PACKET_DEPTH     = 8,
  parameter WAIT_TICKS       = 100
)
(
  input logic clk,
  input logic rst,

  input  dev_t dev,
  input  port_t port,

  ipv4.in_rx  rx,
  ipv4.out_tx tx,

  input  logic [7:0] din,
  input  logic       vin,
  output logic       cts,
  input  logic       snd,

  output logic [7:0] dout,
  output logic       vout,

  output logic  connected,
  input  logic  connect, 
  input  logic  listen,  
  input  ipv4_t rem_ipv4,
  input  port_t rem_port
);

tcp tcp_tx(.*);
tcp tcp_rx(.*);

tcb_t tcb;

queue_if #($bits(byte), RAM_DEPTH) queue_ram (.*);
queue_if #($bits(byte), RAM_DEPTH) queue     (.*);

tcp_vlg_rx tcp_vlg_rx_inst (  
  .clk  (clk),
  .rst  (rst),
  .port (port),
  .rx   (rx), // ipv4
  .tcp  (tcp_rx) // stripped from ipv4, raw tcp
);

tcp_vlg_engine tcp_vlg_engine_inst (
  .clk           (clk),
  .rst           (rst),
  .dev           (dev),
  .port          (port),
  .tcb           (tcb),
  .rx            (tcp_rx),
  .tx            (tcp_tx),     // server -> tx
  .vout          (vout),  //in. packet ready in queue
  .dout          (dout),  //in. packet ready in queue

  .queue         (queue),
  // tcp control
  .connected     (connected),  // this flag indicated connection status as well as selects header to pass to tcp_tx
  .connect       (connect), 
  .listen        (listen),  
  .rem_ipv4      (rem_ipv4),
  .rem_port      (rem_port)
);

tcp_vlg_tx_queue #(
  .MAX_PAYLOAD_LEN  (MAX_PAYLOAD_LEN),
  .RETRANSMIT_TICKS (RETRANSMIT_TICKS),
  .RETRANSMIT_TRIES (RETRANSMIT_TRIES),
  .RAM_DEPTH        (RAM_DEPTH),
  .PACKET_DEPTH     (PACKET_DEPTH),
  .WAIT_TICKS       (WAIT_TICKS)
) tcp_vlg_tx_queue_inst (
  .clk           (clk),
  .rst           (rst),
  .dev           (dev),
    // user interface
  .in_d          (din),
  .in_v          (vin),
  .cts           (cts),
  .snd           (snd),
  .connected     (connected),
  // tcp tx status
  .tx_busy       (tcp_tx.busy),
  .tx_done       (tcp_tx.done),

  .tcb           (tcb),
  .queue         (queue),
  .queue_ram     (queue_ram)
);

tcp_vlg_tx #(
  .RAM_DEPTH (RAM_DEPTH)
) tcp_vlg_tx_inst (  
  .clk           (clk),
  .rst           (rst),
  .tx            (tx),
  .tcp           (tcp_tx),
  .queue_ram     (queue_ram),
  .req           ()
);

endmodule
