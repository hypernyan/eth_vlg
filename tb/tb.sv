`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;

import eth_vlg_pkg::*;

module tb (); 

typedef enum logic {
	idle_s,
	tx_s
} fsm_t;

logic clk = 0;
logic rst = 1;
logic send = 0;
initial #100 rst = 0;
always #4 clk <= ~clk;
///////////////////////
// Configure devices //
///////////////////////
dev_t local_dev;
dev_t remote_dev;

assign local_dev.mac_addr  = 48'h485b3907fe18;
assign local_dev.ipv4_addr = 32'hc0a8010f;
assign local_dev.udp_port  = 1000;
assign local_dev.tcp_port  = 1001;

localparam [47:0] SERVER_MAC_ADDR  = 48'hdeadbeef01;
localparam [31:0] SERVER_IPV4_ADDR = 32'hc0a80101;
localparam [15:0] SERVER_TCP_PORT  = 1001;

localparam [47:0] CLIENT_MAC_ADDR  = 48'habcdef02;
localparam [31:0] CLIENT_IPV4_ADDR = 32'hc0a80115;
localparam [15:0] CLIENT_TCP_PORT  = 1000;

phy phy (.*);
phy phy_rx (.*);
phy phy_tx (.*);


udp udp_cli(.*);
udp udp_srv(.*);
tcp tcp_rx(.*);
tcp tcp_tx(.*);
logic [7:0] tcp_cli_din, tcp_srv_din;
logic tcp_cli_vin, tcp_srv_vin;

logic [7:0] cli_dout;
logic cli_vout;
logic [7:0] srv_dout;
logic srv_vout;

logic cli_connect; 
logic cli_connected; 
logic cli_listen;
ipv4_t cli_rem_ipv4 = SERVER_IPV4_ADDR;
port_t cli_rem_port;

logic  srv_connect; 
logic  srv_connected; 
logic  srv_listen;
ipv4_t srv_rem_ipv4;
port_t srv_rem_port;

assign cli_rem_port = SERVER_TCP_PORT;
assign srv_rem_port = CLIENT_TCP_PORT;

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

assign phy_rxd = phy_rx.d;
assign phy_rxv = phy_rx.v;

assign phy_txd = phy_tx.d;
assign phy_txv = phy_tx.v;

fsm_t cli_fsm, srv_fsm; 
//logic [7:0] test_data_cli_tx [0:TEST_DATA_SIZE_CLI-1];
//logic [7:0] test_data_cli_tx [0:TEST_DATA_SIZE_SRV-1];

// initial begin
// 	for (int i = 0; i < TEST_DATA_SIZE_CLI; i++) begin
// 		test_data_cli_tx[i] = $urandom(1);
// 		test_data_srv_tx[i] = $urandom(2);
// 	end
// end

// Client logic

eth_vlg #(
	.IPV4_ADDR (CLIENT_IPV4_ADDR),
	.MAC_ADDR  (CLIENT_MAC_ADDR)
) cli_inst
(
	.clk    (clk),
	.rst    (rst),
	.phy_rx (phy_rx),
	.phy_tx (phy_tx),

	.udp_tx (udp_cli),
	.udp_rx (udp_cli),
	
	.tcp_din  (tcp_cli_din),
	.tcp_vin  (tcp_cli_vin),
	.tcp_cts  (tcp_cli_cts),

	.tcp_dout (cli_dout),
	.tcp_vout (cli_vout),
	
	.connect   (cli_connect), 
	.connected (cli_connected), 
	.listen    (cli_listen),  
	.rem_ipv4  (cli_rem_ipv4),
	.rem_port  (cli_rem_port)
);
/*
task automatic connect ();
	input ipv4_t ipv4_addr;
	ref connect, connected;
	input int timeout;
	int timeout_counter;
	connect = 1;

endtask : connect

task automatic send_file ();
	input string filename;
	ref clk;
	ref bit [7:0] dat;
	ref bit       val;
	ref bit       cts;

endtask

task receive_file ();

endtask

task compare_files ();

endtask

always @ (posedge clk) begin
	if (rst) begin
		cli_ctr <= 0;
		cli_tx_ctr <= 0;
		tcp_cli_vin <= 0;
		tcp_cli_din <= 0;
		cli_fsm <= idle_s;
	end
	else begin
		if (tcp_cli_cts) begin
			tcp_cli_din <= test_data_cli_tx[cli_tx_ctr];
			
		end
		endcase
	end
//	else tcp_vin <= 0;
end
*/

eth_vlg #(
	.IPV4_ADDR (SERVER_IPV4_ADDR),
	.MAC_ADDR  (SERVER_MAC_ADDR)
) srv_inst
(
	.clk    (clk),
	.rst    (rst),
	.phy_rx (phy_tx),
	.phy_tx (phy_rx),

	.udp_tx (udp_srv),
	.udp_rx (udp_srv),
	
	.tcp_din  (tcp_srv_din),
	.tcp_vin  (tcp_srv_vin),
	.tcp_cts  (tcp_srv_cts),

	.tcp_dout (srv_dout),
	.tcp_vout (srv_vout),
	
	.connect   (srv_connect), 
	.connected (srv_connected), 
	.listen    (srv_listen),  
	.rem_ipv4  (srv_rem_ipv4),
	.rem_port  (srv_rem_port)
);


// srv
always @ (posedge clk) begin
	if (rst) begin
		srv_ctr <= 0;
		srv_tx_ctr <= 0;
		tcp_srv_vin <= 0;
		tcp_srv_din <= 0;
		srv_fsm <= tx_s;
	end
	else begin
		case (srv_fsm)
			idle_s : begin
				srv_ctr <= (srv_ctr == 10000) ? srv_ctr : srv_ctr + 1;
			//	if (tcp_srv_cts) srv_fsm <= tx_s;
				tcp_srv_vin <= 0;
				srv_tx_ctr <= 0;
			end
			tx_s : begin
				srv_ctr <= 0;
				srv_tx_ctr <= srv_tx_ctr + 1;
				if (tcp_srv_cts && srv_tx_ctr[3:0] == 4'h0) begin
					tcp_srv_din <= tcp_srv_din + 1;
					tcp_srv_vin <= 1;
				end
				else begin
					tcp_srv_vin <= 0;
				end
			end
		endcase
	end
//	else tcp_vin <= 0;
end

endmodule
