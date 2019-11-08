import ip_vlg_pkg::*;
import eth_vlg_pkg::*;
import mac_vlg_pkg::*;

module ip_vlg_top #(
	parameter NUM_PROTOCOLS = 2
) (
	input logic clk,
	input logic rst,
	mac.in      rx,
	mac.out     tx,
	input dev_t dev,
	// Connects to ARP table
	output ipv4_t     ipv4_req,
	input  mac_addr_t mac_rsp,
	input  logic      arp_val,
	input  logic      arp_err,
	// Raw UDP
	udp.in  udp_tx,
	udp.out udp_rx
);

ipv4 ipv4_tx(.*);
ipv4 ipv4_rx(.*);
ipv4 icmp_ipv4_tx(.*);
ipv4 udp_ipv4_tx(.*);

ipv4_hdr_t [1:0] tx_ipv4_hdr_v;
mac_hdr_t  [1:0] tx_mac_hdr_v;

assign tx_ipv4_hdr_v = {udp_ipv4_tx.ipv4_hdr, icmp_ipv4_tx.ipv4_hdr};
assign tx_mac_hdr_v  = {udp_ipv4_tx.mac_hdr,  icmp_ipv4_tx.mac_hdr};

logic [1:0] act_ms;
logic rdy;
logic avl;

logic       ipv4_tx_v;
logic [7:0] ipv4_tx_d;
logic       ipv4_rx_v;
logic [7:0] ipv4_rx_d;

logic       mac_tx_v;
logic [7:0] mac_tx_d;
logic       mac_rx_v;
logic [7:0] mac_rx_d;

ipv4_vlg ipv4_vlg_inst(
	.clk      (clk),
	.rst      (rst),
	.rst_fifo (rst_fifo),

	.mac_rx   (rx),
	.mac_tx   (tx),
	.dev      (dev),

	.rdy      (rdy),
	.avl      (avl),
	.tx_busy  (ipv4_tx_busy),

	.ipv4_req (ipv4_req),
	.mac_rsp  (mac_rsp),
	.arp_val  (arp_val),
	.arp_err  (arp_err),
	.ipv4_tx  (ipv4_tx),
	.ipv4_rx  (ipv4_rx)
);

ipv4_hdr_t ipv4_rx_hdr;

assign ipv4_tx_v = ipv4_tx.v;
assign ipv4_tx_d = ipv4_tx.d;
assign ipv4_rx_v = ipv4_rx.v;
assign ipv4_rx_d = ipv4_rx.d;
assign ipv4_rx_hdr = ipv4_rx.ipv4_hdr;

assign mac_tx_v = tx.v;
assign mac_tx_d = tx.d;
assign mac_rx_v = rx.v;
assign mac_rx_d = rx.d;

// Protocol 1
icmp_vlg icmp_vlg_inst (
	.clk  (clk),
	.rst  (rst),
	.rx   (ipv4_rx),
	.dev  (dev),
	.tx   (icmp_ipv4_tx)
);

// Protocol 2
udp_vlg udp_vlg_inst (
	.clk    (clk),
	.rst    (rst),
	.rx     (ipv4_rx),
	.tx     (udp_ipv4_tx),
	.udp_tx (udp_tx),
	.udp_rx (udp_rx),
	.dev    (dev)
);
// Number of protocols under ipv4 is 2 (NUM_PROTOCOLS = 2)
// Logic selecting appropriate header for ipv4_tx. It uses buf_mng to queue 
wor [NUM_PROTOCOLS:0] ind; // index
logic [NUM_PROTOCOLS-1:0] act_ms_reg;
logic [NUM_PROTOCOLS-1:0] rst_fifo_vect;

genvar i;
generate
	for (i = 0; i < NUM_PROTOCOLS; i = i + 1) begin : gen_index
		assign ind = (act_ms[i] == 1'b1) ? i : 0;
		assign rst_fifo_vect[i] = (rst_fifo & act_ms[i]);
	end
endgenerate

assign ipv4_tx.ipv4_hdr = tx_ipv4_hdr_v[ind];
assign ipv4_tx.mac_hdr  = tx_mac_hdr_v[ind];

logic avl_reg;
always @ (posedge clk) begin
	act_ms_reg <= act_ms;
	avl_reg <= avl;
end

buf_mng #(
	.W (8),
	.N (2),
	.D ({32'd10, 32'd8}),
	.RWW (0)
)
buf_mng_inst (
	.clk (clk),
	.rst (rst),
	.rst_fifo (rst_fifo_vect),

	.v_i ({udp_ipv4_tx.v, icmp_ipv4_tx.v}),
	.d_i ({udp_ipv4_tx.d, icmp_ipv4_tx.d}),

	.v_o (ipv4_tx.v),
	.d_o (ipv4_tx.d),
	.eof (ipv4_tx.eof),
	.rdy (rdy),      // ipv4_tx is ready to accept data
	.avl (avl),      // data available to ipv4_tx
	.act_ms (act_ms) // tells which header to pass to ipv4_tx
);

endmodule
