
module top (
	output wire       phy_gtx_clk,
	input  wire       phy_rx_clk, 

	output wire       phy_tx_err, 
	output wire       phy_tx_val, 
	output wire [7:0] phy_tx_dat, 

	input  wire       phy_rx_err, 
	input  wire       phy_rx_val,
	input  wire [7:0] phy_rx_dat,

	output logic phy_rst_n,
	output logic phy_pwr_en
);

logic [7:0] reset_ctr;
always @ (posedge phy_rx_clk) begin
	reset_ctr <= reset_ctr + 1;
	if (reset_ctr == 100) rst_n <= 1;
end
assign phy_rst_n = 1;
assign phy_pwr_en = 1;

logic [7:0] tcp_din, tcp_dout;
logic tcp_vin, tcp_vout;

phy phy_rx(.*);
phy phy_tx(.*);

udp udp_rx(.*);
udp udp_tx(.*);

assign phy_rx.d = phy_rx_dat;
assign phy_rx.v = phy_rx_val;
assign phy_rx.e = phy_rx_err;

assign phy_tx_dat  = phy_tx.d;
assign phy_tx_val  = phy_tx.v;
assign phy_tx_err  = phy_tx.e;
assign phy_gtx_clk = phy_rx_clk;

logic rst;
eth_vlg #(
	.MAC_ADDR  (48'h107b444fd012),
	.IPV4_ADDR (32'hc0a800d5)
) eth_vlg_inst
(
	.phy_rx (phy_rx),
	.phy_tx (phy_tx),

	.clk (phy_rx_clk),
	.rst (!rst_n),

	.udp_tx (udp_tx),
	.udp_rx (udp_rx),

	.tcp_din (tcp_din),
	.tcp_vin (tcp_vin),
	.tcp_cts (tcp_cts),

	.tcp_dout (tcp_dout),
	.tcp_vout (tcp_vout),
	// 'server'
	.connected (connected), 
	.listen    (1'b1), // 
	// 'client'
	.connect   (1'b0), //!connected && (ctr == 12500000)), 
	.rem_ipv4  (32'hc0a80065), // remote ipv4
	.rem_port  (1000) // remote port
);

always @ (posedge phy_rx_clk) begin
	tcp_din <= tcp_din + 1;
	tcp_vin <= (tcp_cts && tcp_din[1:0] == 2'b00); 
end

endmodule
