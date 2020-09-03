`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;

import eth_vlg_pkg::*;

class user_logic;
  file_t file;
  task automatic test ();
	input int payload_length;
	input real packet_loss;
	input int tx_buffer_size;
	input real packet_loss;
	input real packet_loss;
	$display("Starting TCP test...");
	$display("Interface speed: 1 Gbit.");
	$display("MTU: 1460 bytes.");
	$display("Server transmit buffer size: %d bytes", 2**tx_buffer_size);
	$display("Server receive buffer size: %d bytes",  2**rx_buffer_size);
	$display("Client transmit buffer size: %d bytes", 2**tx_buffer_size);
	$display("Client receive buffer size: %d bytes",  2**rx_buffer_size);
	$display("====================================");
	$display("Target transmission speed: 500Mbps");
	$display("Server to client payload length: %d bytes", payload_length);
	connect(
	  connect_cli, 
	  connected_cli, 
	  listen_cli,  
	  rem_ipv4_cli,
	  rem_port_cli);
	transfer_file();
  );
	task automatic connect ();
	  input logic  connect_cli;
	  input logic  connected_cli; 
	  input logic  listen_cli;
	  input ipv4_t rem_ipv4_cli;
	  input port_t rem_port_cli;

	  input logic  connect_srv;
	  input logic  connected_srv; 
	  input logic  listen_srv;
	  input ipv4_t rem_ipv4_srv;
	  input port_t rem_port_srv;

		input int timeout;
		int timeout_counter;
		connect = 1;
		fork : f
		begin
			@ (posedge connected);
			$display("> Connected.");
			disable f;
		end
		begin
			always @ (posedge clk) timeout_ctr <= timeout_ctr + 1;
			if (timeout_ctr) $display("> Connection timeout.");
		end
		end
	endtask : connect
endclass : user_logic

module tb (); 

logic clk = 0;
logic rst = 1;
logic send = 0;
initial #100 rst = 0;
always #4 clk <= ~clk;

///////////////////////
// Configure devices //
///////////////////////

localparam [47:0] SERVER_MAC_ADDR  = 48'hdeadbeef01;
localparam [31:0] SERVER_IPV4_ADDR = 32'hc0a80101;
localparam [15:0] SERVER_TCP_PORT  = 1001;
localparam        SERVER_N_TCP     = 4;

localparam [47:0] CLIENT_MAC_ADDR  = 48'habcdef02;
localparam [31:0] CLIENT_IPV4_ADDR = 32'hc0a80115;
localparam [15:0] CLIENT_TCP_PORT  = 1000;
localparam        CLIENT_N_TCP     = 4;

phy phy (.*);
phy phy_rx_cli (.*);
phy phy_rx_srv (.*);
phy phy_tx_cli (.*);
phy phy_tx_srv (.*);

logic [7:0] tcp_cli_din, tcp_srv_din;
logic tcp_cli_vin, tcp_srv_vin;

logic [7:0] cli_dout;
logic cli_vout;
logic [7:0] srv_dout;
logic srv_vout;

logic  connect_cli,   connect_srv; 
logic  connected_cli, connected_srv; 
logic  listen_cli,    listen_srv;
ipv4_t rem_ipv4_cli,  rem_ipv4_srv;
port_t rem_port_cli,  rem_port_srv;

assign rem_ipv4_cli = CLIENT_IPV4_ADDR
assign rem_ipv4_srv = SERVER_IPV4_ADDR
assign cli_rem_port_cli = SERVER_TCP_PORT;
assign srv_rem_port_srv = CLIENT_TCP_PORT;

assign srv_connect = 1'b0;
initial #1000 cli_connect = 1'b1;

assign cli_listen = 1'b0;
initial #1000 srv_listen = 1'b1;

logic tcp_cli_cts, tcp_srv_cts;

logic [$clog2(12500)-1:0] cli_ctr, srv_ctr;
logic [10:0] cli_tx_ctr, srv_tx_ctr;

logic [7:0] phy_rxd;
logic       phy_rxv;

logic [7:0] phy_txd;
logic       phy_txv;

assign phy_rxd_cli = phy_rx_cli.d;
assign phy_rxv_cli = phy_rx_cli.v;

assign phy_txd = phy_rx_cli.d;
assign phy_txv = phy_rx_cli.v;

fsm_t cli_fsm, srv_fsm; 

initial begin
	user_logic user_cli = new();
	user_logic user_srv = new();
	user_srv.listen(CLI_IPV4, CLI_PORT, );
end

typedef struct (
	real loss; // ~ %of packets completely lost
	real corrupt;
) phy_param_t;

ethernet_phy ethernet_cli_to_srv (
	.clk        (),
	.phy_params (),
	.in_v       (),
	.in_d       (),
	.out_v      (),
	.out_d      ()
);

ethernet_phy ethernet_srv_to_cli (
	.clk        (),
	.phy_params (),
	.in_v       (phy_tx_srv.v),
	.in_d       (phy_tx_srv.d),
	.out_v      (phy_rx_cli.v),
	.out_d      (phy_rx_cli.d)
);

// Client logic

eth_vlg #(
	.IPV4_ADDR (CLIENT_IPV4_ADDR),
	.MAC_ADDR  (CLIENT_MAC_ADDR)
) cli_inst
(
	.clk       (clk),
	.rst       (rst),
	.phy_rx    (phy_rx_cli),
	.phy_tx    (phy_tx_cli),
   
	.udp_tx    (udp_cli),
	.udp_rx    (udp_cli),
	
	.tcp_din   (tcp_din_cli),
	.tcp_vin   (tcp_vin_cli),
	.tcp_cts   (tcp_cts_cli),
 
	.tcp_dout  (dout_cli),
	.tcp_vout  (vout_cli),
	
	.connect   (connect_cli), 
	.connected (connected_cli), 
	.listen    (listen_cli),  
	.rem_ipv4  (rem_ipv4_cli),
	.rem_port  (rem_port_cli)
);


eth_vlg #(
	.IPV4_ADDR (SERVER_IPV4_ADDR),
	.MAC_ADDR  (SERVER_MAC_ADDR)
) srv_inst
(
	.clk       (clk),
	.rst       (rst),
	.phy_rx    (phy_rx_srv),
	.phy_tx    (phy_tx_srv),
 
	.udp_tx    (udp_srv),
	.udp_rx    (udp_srv),
	 
	.tcp_din   (tcp_din_srv),
	.tcp_vin   (tcp_vin_srv),
	.tcp_cts   (tcp_cts_srv),
 
	.tcp_dout  (dout_srv),
	.tcp_vout  (vout_srv),
	
	.connect   (connect_srv), 
	.connected (connected_srv), 
	.listen    (listen_srv),  
	.rem_ipv4  (rem_ipv4_srv),
	.rem_port  (rem_port_srv)
);

endmodule
