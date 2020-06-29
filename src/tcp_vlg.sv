
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
  parameter TX_QUEUE_DEPTH = 8
)
(
  input logic clk,
  input logic rst,

  output logic cts,
  input  dev_t dev,

  ipv4.in  rx,
  ipv4.out tx,
  
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


tcp tcp_tx(.*);
tcp tcp_rx(.*);

logic [31:0] queue_seq;
logic [15:0] queue_len;
logic [31:0] queue_cs;
logic [7:0] queue_data;
logic [TX_QUEUE_DEPTH-1:0] queue_addr;

tcb_t tcb;
logic force_fin;

tcp_vlg_rx tcp_vlg_rx_inst (  
  .clk (clk),
  .rst (rst),
  .dev (dev),
  .rx  (rx), // ipv4
  .tcp (tcp_rx) // stripped from ipv4, raw tcp
);

tcp_server tcp_server_inst (
  .clk           (clk),
  .rst           (rst),
  .dev           (dev),
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
  .MTU              (8000),
  .RETRANSMIT_TICKS (10000),
  .DEPTH            (TX_QUEUE_DEPTH),
  .MAX_PACKET_DEPTH (4),
  .WAIT_TICKS       (20)
) tcp_tx_queue_inst (
  .clk       (clk),
  .rst       (rst),
  .dev (dev),
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
  .payload_chsum  (queue_cs),  // packet's len
  .connected      (connected),
  .force_fin      (force_fin),
  .flush_queue    (flush_queue),  
  .queue_flushed  (queue_flushed)
);

tcp_vlg_tx #(
  .TX_QUEUE_DEPTH (TX_QUEUE_DEPTH)
) tcp_vlg_tx_inst (  
  .clk (clk),
  .rst (rst),
  .dev (dev),
  .tx  (tx),
  .tcp (tcp_tx),
  .queue_data (queue_data), //in. data addr queue_addr 
  .queue_addr (queue_addr) //out.
);

endmodule