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
phy phy_rx (.*);
phy phy_tx (.*);


udp udp_cli(.*);
udp udp_srv(.*);
tcp tcp_rx(.*);
tcp tcp_tx(.*);
logic [7:0] tcp_din;
logic tcp_vin;
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
	
	.tcp_din  (tcp_din),
	.tcp_vin  (tcp_vin),
	.tcp_cts  (tcp_cli_cts),

	.tcp_dout (cli_dout),
	.tcp_vout (cli_vout),
	
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
	.phy_rx (phy_tx),
	.phy_tx (phy_rx),

	.udp_tx (udp_srv),
	.udp_rx (udp_srv),
	
	.tcp_din  (tcp_din),
	.tcp_vin  (tcp_vin),
	.tcp_cts  (tcp_srv_cts),

	.tcp_dout (srv_dout),
	.tcp_vout (srv_vout),
	
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
logic [7:0] phy_rxd;
logic       phy_rxv;

logic [7:0] phy_txd;
logic       phy_txv;

assign phy_rxd = phy_rx.d;
assign phy_rxv = phy_rx.v;

assign phy_txd = phy_tx.d;
assign phy_txv = phy_tx.v;

hexdump #(
	.FILENAME ("dump.txt")
) hexdump_inst (
	.clk (clk),
	.vin (phy_tx.v),
	.din (phy_tx.d)
);

endmodule
