import eth_vlg_pkg::*;
import mac_vlg_pkg::*;

module eth_vlg #(
	parameter mac_addr_t  MAC_ADDR  = 'b0,
	parameter ipv4_t IPV4_ADDR = 'b0
)
(
	phy.in  phy_rx,
	phy.out phy_tx,

	input logic clk,
	input logic rst,

	udp.in  udp_tx,
	udp.out udp_rx,

	input  logic [7:0] tcp_din,
	input  logic       tcp_vin,
	output logic       tcp_cts,

	output logic [7:0] tcp_dout,
	output logic       tcp_vout,
	
	input  logic  connect, 
	output logic  connected, 
	input  logic  listen,  
	input  ipv4_t rem_ipv4,
	input  port_t rem_port
);

mac mac_rx(.*);
mac mac_tx(.*);
mac mac_arp_tx(.*);
mac mac_ipv4_tx(.*);

dev_t dev;
assign dev.mac_addr  = MAC_ADDR;
assign dev.ipv4_addr = IPV4_ADDR;
assign dev.udp_port  = 16'h0203;
assign dev.tcp_port  = 1001;

logic [1:0] cur, act_ms, rst_fifo_vect;
mac_hdr_t arp_mac_hdr_tx;
mac_addr_t mac_rsp;
ipv4_t ipv4_req;
logic rdy, arp_val, arp_err, rst_fifo_ip, rst_fifo_arp, rst_fifo;

mac_hdr_t [1:0] mac_hdr_v;
assign mac_hdr_v = {mac_ipv4_tx.hdr, mac_arp_tx.hdr};

mac_vlg mac_vlg_inst (
	.clk      (clk),
	.rst      (rst),
	.rst_fifo (rst_fifo),
	.dev      (dev),
	.phy_rx   (phy_rx),
	.phy_tx   (phy_tx),

	.rx       (mac_rx),
	.tx       (mac_tx),
	.avl      (avl),
	.rdy      (rdy)
);

ip_vlg_top ip_vlg_top_inst (
	.clk (clk),
	.rst (rst),

	.dev (dev),

	.ipv4_req (ipv4_req),
	.mac_rsp  (mac_rsp),
	.arp_val  (arp_val),
	.arp_err  (arp_err),

	.rx (mac_rx),
	.tx (mac_ipv4_tx),

	.udp_tx (udp_tx),
	.udp_rx (udp_rx),

	.tcp_din  (tcp_din),
	.tcp_vin  (tcp_vin),
	.tcp_cts  (tcp_cts),

	.tcp_dout (tcp_dout),
	.tcp_vout (tcp_vout),
	
	.connect   (connect), 
	.connected (connected), 
	.listen    (listen),  
	.rem_ipv4  (rem_ipv4),
	.rem_port  (rem_port)
);

arp_vlg arp_vlg_inst (
	.clk      (clk),
	.rst      (rst),

	.dev      (dev),
	.ipv4_req (ipv4_req),
	.mac_rsp  (mac_rsp),
	.arp_val  (arp_val),
	.arp_err  (arp_err),
	.rx       (mac_rx),
	.tx       (mac_arp_tx)
);

assign mac_ipv4_tx.busy = mac_tx.busy;
assign mac_arp_tx.busy = mac_tx.busy;

wor ind;
//wire ind;
genvar i;
generate
	for (i = 0; i < 2; i = i + 1) begin : gen
		assign ind = (act_ms[i] == 1'b1) ? i : 0;
	end
endgenerate
always @ (posedge clk) mac_tx.hdr <= mac_hdr_v[ind];

assign rst_fifo_vect = (rst_fifo && act_ms) ? 2'b11 : 2'b00;

buf_mng #(
	.W (8),
	.N (2),
	.D ({32'd8, 32'd8}),
	.RWW (1)
) buf_mng_inst (
	.clk      (clk),
	.rst      (rst),
	.rst_fifo (rst_fifo_vect),

	.v_i      ({mac_ipv4_tx.v, mac_arp_tx.v}),
	.d_i      ({mac_ipv4_tx.d, mac_arp_tx.d}),

	.v_o      (mac_tx.v),
	.d_o      (mac_tx.d),
	.eof      (),
	.rdy      (rdy),
	.avl      (avl),
	.act_ms   (act_ms)
);

endmodule