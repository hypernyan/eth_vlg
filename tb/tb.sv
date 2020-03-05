`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;

import eth_vlg_pkg::*;

module tb (); 

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
phy phy_srv2cli (.*);
phy phy_cli2srv (.*);


udp udp_cli(.*);
udp udp_srv(.*);
tcp tcp_rx(.*);
tcp tcp_tx(.*);
logic [7:0] tcp_din;
logic tcp_vin;
logic [7:0] tcp_dout;
logic tcp_vout;

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
eth_vlg #(
	.IPV4_ADDR (CLIENT_IPV4_ADDR),
	.MAC_ADDR  (CLIENT_MAC_ADDR)
) cli_inst
(
	.clk    (clk),
	.rst    (rst),
	.phy_rx (phy_srv2cli),
	.phy_tx (phy_cli2srv),

	.udp_tx (udp_cli),
	.udp_rx (udp_cli),
	
	.tcp_din  (tcp_din),
	.tcp_vin  (tcp_vin),
	.tcp_cts  (tcp_cli_cts),

	.connect   (cli_connect), 
	.connected (cli_connected), 
	.listen    (cli_listen),  
	.rem_ipv4  (cli_rem_ipv4),
	.rem_port  (cli_rem_port)
);

eth_vlg #(
	.IPV4_ADDR (SERVER_IPV4_ADDR),
	.MAC_ADDR  (SERVER_MAC_ADDR)
) srv_inst
(
	.clk    (clk),
	.rst    (rst),
	.phy_rx (phy_cli2srv),
	.phy_tx (phy_srv2cli),

	.udp_tx (udp_srv),
	.udp_rx (udp_srv),
	
	.tcp_din  (tcp_din),
	.tcp_vin  (tcp_vin),
	.tcp_cts  (tcp_srv_cts),

	.connect   (srv_connect), 
	.connected (srv_connected), 
	.listen    (srv_listen),  
	.rem_ipv4  (srv_rem_ipv4),
	.rem_port  (srv_rem_port)
);


logic [$clog2(12500)-1:0] ctr;
logic [10:0] tx_ctr;

enum logic {
	idle_s,
	tx_s
} fsm;

logic tcp_cts;
always @ (posedge clk) begin
	if (rst) begin
		ctr <= 0;
		tx_ctr <= 0;
		tcp_vin <= 0;
		tcp_din <= 0;
		fsm <= idle_s;
	end
	else begin
		case (fsm)
			idle_s : begin
				ctr <= (ctr == 10000) ? ctr : ctr + 1;
				if (ctr == 10000 && tcp_srv_cts) fsm <= tx_s;
				tcp_vin <= 0;
				tx_ctr <= 0;
			end
			tx_s : begin
				ctr <= 0;
				tx_ctr <= tx_ctr + 1;
				if (tx_ctr == 1400) fsm <= idle_s;
				tcp_vin <= 1;
				tcp_din <= tcp_din + 1;
			end
		endcase
	end
//	else tcp_vin <= 0;
end
logic [7:0] phy_srv2cli_d;
logic       phy_srv2cli_v;

logic [7:0] phy_cli2srv_d;
logic       phy_cli2srv_v;

assign phy_srv2cli_d = phy_srv2cli.d;
assign phy_srv2cli_v = phy_srv2cli.v;

assign phy_cli2srv_d = phy_cli2srv.d;
assign phy_cli2srv_v = phy_cli2srv.v;

hexdump #(
	.FILENAME ("dump.txt")
) hexdump_inst (
	.clk (clk),
	.vin (phy_cli2srv.v),
	.din (phy_cli2srv.d)
);

endmodule
