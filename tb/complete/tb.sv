`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
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

localparam [47:0] SERVER_MAC_ADDR  = 48'hdeadbeef01;
localparam [31:0] SERVER_IPV4_ADDR = 32'hc0a80101;
localparam [15:0] SERVER_UDP_PORT  = 1200;

assign remote_dev.mac_addr  = SERVER_MAC_ADDR; 
assign remote_dev.ipv4_addr = SERVER_IPV4_ADDR;
assign remote_dev.udp_port  = SERVER_UDP_PORT;

phy phy (.*);
phy phy_rx (.*);
phy phy_tx (.*);

pkt_gen pkt_gen_inst (
	.clk         (clk),
	.rst         (rst),

	.local_dev     (local_dev),
	.srv_ipv4_addr (SERVER_IPV4_ADDR),
	.srv_udp_port  (SERVER_UDP_PORT),
	.phy_rx        (phy_tx),
	.phy_tx        (phy_rx)
);

udp udp(.*);

eth_vlg #(
	.IPV4_ADDR (SERVER_IPV4_ADDR),
	.MAC_ADDR  (SERVER_MAC_ADDR),
	.UDP_PORT  (SERVER_UDP_PORT)
) dut
(
	.clk    (clk),
	.rst    (rst),
	.phy_rx (phy_rx),
	.phy_tx (phy_tx),

	.udp_tx (udp),
	.udp_rx (udp)
);

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
