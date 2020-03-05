
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
	logic [31:0]  payload_checksum;
	
	modport in  (input  d, v, sof, eof, payload_length, payload_checksum, err, tcp_hdr, tcp_opt_hdr, tcp_hdr_v, ipv4_hdr, mac_hdr, rdy, output req, done, busy);
	modport out (output d, v, sof, eof, payload_length, payload_checksum, err, tcp_hdr, tcp_opt_hdr, tcp_hdr_v, ipv4_hdr, mac_hdr, rdy, input  req, done, busy);
endinterface


module tcp_vlg #(
	parameter TX_QUEUE_DEPTH = 14,
	parameter MTU            = 9000
)
(
	input logic clk,
	input logic rst,

	input  dev_t dev,

	ipv4.in  rx,
	ipv4.out tx,
	
	input  logic [7:0] din,
	input  logic       vin,
	output logic       cts,
	
	output logic [7:0] dout,
	output logic       vout,

	output logic  connected,
	input  logic  connect, 
	input  logic  listen,  
	input  ipv4_t rem_ipv4,
	input  port_t rem_port
);

//                    ____________________________________
//        _______    |               srv                  |    _______
//       |       |   |                                    |   |       |
//       |       |<------------------req----------------------|       |
//       |    ___|-------------------rdy--------------------->|       |
//       |   |rst|<------------------done---------------------|       |
//       |       |   |                |             _     |   |       |
//       |       |   |                |            | \    |   |       |
// user  |       |   |   seq, data>   |            |  \   |   |       |
// =====>| queue |================================>|   |  |   |  tx   |
// data  |       |   |   <ack         |            |   |  |   |       |
//       |       |   |              __V__          |   |=====>|       |
//       |       |   |     hdr     |     |   hdr   |   |  |   |_______|
//       |       |<================| FSM |========>|   |  | 
//       |_______|   |     (seq,   |_____| hdr val |  /   |
//                   |     ack)       |            |_/    |
//                   |                |__connected__|     |
//                   |____________________________________|

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

tcp_server #(
	.TX_QUEUE_DEPTH (TX_QUEUE_DEPTH)
) tcp_server_inst (
    .clk           (clk),
    .rst           (rst),
	.dev           (dev),
    .ipv4          (rx),
	.tcb           (tcb),
    .rx            (tcp_rx),
    .queue_val     (queue_val),  // packet ready in queue
    .queue_seq     (queue_seq),  // packet's seq
    .queue_len     (queue_len),  // packet's len
    .queue_cs      (queue_cs),   // packet's checksum
	.flush_queue   (flush_queue),  
	.queue_flushed (queue_flushed), 
    .tx            (tcp_tx),        // server -> tx
	.connected     (connected),     // connection status
	.force_fin     (force_fin),     // queue will force connection close if failed retransmission 

	// tcp control
	.connect  (connect), 
	.listen   (listen),  
	.rem_ipv4 (rem_ipv4),
	.rem_port (rem_port)
);

tcp_tx_queue #(
	.MTU              (MTU),
	.RETRANSMIT_TICKS (300000),
	.RAM_DEPTH        (TX_QUEUE_DEPTH),
	.PACKETS_DEPTH    (8),
	.WAIT_TICKS       (20)
) tcp_tx_queue_inst (
    .clk              (clk),
    .rst              (rst),
    // user interface
	.in_d             (din),
    .in_v             (vin),
    .cts              (cts),
	// tcp tx status
    .tx_busy          (tcp_tx.busy), // queue will wait if tx is busy
	.tx_done          (tcp_tx.done), // queue will begin processing next packet when done sending current
    .rem_ack          (tcb.rem_ack_num), // keep track of remote ack for retransmissions
	// 
    .val              (queue_val), // a packet is ready to be sent
    .req              (queue_req),       //
    .addr             (queue_addr),      //
	.data             (queue_data),      //in. data addr queue_addr 
	// all that's needed to for a tcp packet
    .seq              (queue_seq), // packet's seq
    .len              (queue_len), // packet's len
    .payload_checksum (queue_cs),  // packet's checksum. 
	// queue controls
	.connected        (connected),
    .isn              (tcb.isn),   // initial sequence number to set initial address for queue's buffer
	.force_fin        (force_fin),
	.flush_queue      (flush_queue),  
	.queue_flushed    (queue_flushed)
);

tcp_vlg_rx_queue tcp_vlg_rx_queue_inst (
	.clk       (clk),
	.rst       (rst),
	.dev       (dev),
	.tcp       (tcp_rx),
	.tcb       (tcb),
	.cur_ack   (tcb.loc_ack_num),
	// user interface
	.dout      (dout),
	.vout      (vout),
	.connected (connected)
);

tcp_vlg_tx #(
	.TX_QUEUE_DEPTH (TX_QUEUE_DEPTH)
) tcp_vlg_tx_inst (	
	.clk        (clk),
	.rst        (rst),
	.dev        (dev),
	.tx         (tx),
	.tcp        (tcp_tx),
	.queue_data (queue_data), //in. data addr queue_addr 
    .queue_addr (queue_addr), //out.
    .req        (queue_req) //out.
);

endmodule
