
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

  output logic cts,
  input  dev_t dev,
  input  port_t port,

  ipv4.in_rx  rx,
// Due to inability to generate interfaces, pass as simple ports 
  ipv4.out_tx tx,
  
 //output logic [7:0] d,
 //output logic       v,
 //output logic       sof,
 //output logic       eof,
 //output logic       err,
 //input  logic       busy,
 //input  logic       done,
 //output length_t    payload_length,
 //output ipv4_hdr_t  ipv4_hdr,
 //output mac_hdr_t   mac_hdr,

  input  logic [7:0] din,
  input  logic       vin,
  
  output logic [7:0] dout,
  output logic       vout,

  output logic  connected,
  input  logic  connect, 
  input  logic  listen,  
  input  ipv4_t rem_ipv4,
  input  port_t rem_port
);

//ipv4 tx(.*);
//
//assign d              = tx.d;
//assign v              = tx.v;
//assign sof            = tx.sof;
//assign eof            = tx.eof;
//assign err            = tx.err;
//assign tx.busy        = busy;
//assign tx.done        = done;
//assign payload_length = tx.payload_length;
//assign ipv4_hdr       = tx.ipv4_hdr;
//assign mac_hdr        = tx.mac_hdr;

tcp tcp_tx(.*);
tcp tcp_rx(.*);

logic [31:0] queue_seq;
logic [15:0] queue_len;
logic [31:0] queue_cs;
logic [7:0] queue_data;
logic [RAM_DEPTH-1:0] queue_addr;

tcb_t tcb;
logic force_fin;

tcp_vlg_rx tcp_vlg_rx_inst (  
  .clk (clk),
  .rst (rst),
  .port (port),
  .rx  (rx), // ipv4
  .tcp (tcp_rx) // stripped from ipv4, raw tcp
);

tcp_server tcp_server_inst (
  .clk           (clk),
  .rst           (rst),
  .dev           (dev),
  .port          (port),
  .ipv4          (rx),
  .tcb           (tcb),
  .rx            (tcp_rx),
  .tx            (tcp_tx),     // server -> tx
  .vout          (vout),  //in. packet ready in queue
  .dout          (dout),  //in. packet ready in queue
  .queue_pend    (queue_pend),  //in. packet ready in queue
  .queue_seq     (queue_seq),  // packet's seq
  .queue_len     (queue_len),  // packet's len
  .queue_cs      (queue_cs),  // packet's chsum
  .flush_queue   (flush_queue),  
  .queue_flushed (queue_flushed),
  .connected     (connected),  // this flag indicated connection status as well as selects header to pass to tcp_tx
  .force_fin     (force_fin),

  // tcp control
  .connect  (connect), 
  .listen   (listen),  
  .rem_ipv4 (rem_ipv4),
  .rem_port (rem_port)
);

tcp_vlg_tx_queue #(
  .MAX_PAYLOAD_LEN  (MAX_PAYLOAD_LEN),
  .RETRANSMIT_TICKS (RETRANSMIT_TICKS),
  .RETRANSMIT_TRIES (RETRANSMIT_TRIES),
  .RAM_DEPTH        (RAM_DEPTH),
  .PACKET_DEPTH     (PACKET_DEPTH),
  .WAIT_TICKS       (WAIT_TICKS)
) tcp_tx_queue_inst (
  .clk       (clk),
  .rst       (rst),
  .dev       (dev),
    // user interface
  .in_d      (din),
  .in_v      (vin),
  .cts       (cts),
  // tcp tx status
  .tx_busy   (tcp_tx.busy),
  .tx_done   (tcp_tx.done),

  .rem_ack        (tcb.rem_ack_num), // keep track of remote ack for retransmissions
  .data           (queue_data), //in. data addr queue_addr 
  .addr           (queue_addr), //out.
  .pending        (queue_pend),  //in. packet ready in queue
  .isn            (tcb.loc_seq_num),  // packet's seq
  .seq            (queue_seq),  // packet's seq
  .len            (queue_len),  // packet's len
  .payload_chsum  (queue_cs),   // packet's checksum
  .connected      (connected),
  .force_fin      (force_fin),
  .flush_queue    (flush_queue),  
  .queue_flushed  (queue_flushed)
);

tcp_vlg_tx #(
  .RAM_DEPTH (RAM_DEPTH)
) tcp_vlg_tx_inst (  
  .clk (clk),
  .rst (rst),
  .tx  (tx),
  .tcp (tcp_tx),
  .queue_data (queue_data), //in. data addr queue_addr 
  .queue_addr (queue_addr) //out.
);

endmodule
