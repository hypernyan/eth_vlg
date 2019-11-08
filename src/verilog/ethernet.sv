import eth_vlg_pkg::*;

module ethernet (
	input  wire  phy_rx_clk,
	output wire  phy_gtx_clk,
	input  wire  clk_125m,
	input  wire  clk_125m_shift,
	// Clock for MDIO
	input  wire  clk_mdio,
	// Synchronous reset
	input  wire rst,

	input  wire arst,
	
	input  logic [7:0]  phy_rx_dat,
	input  logic        phy_rx_val,
	input  logic        phy_rx_err,

	output logic [7:0]  phy_tx_dat,
	output logic        phy_tx_val,
	output logic        phy_tx_err,

	output wire MDIO,      
	output wire MDC,       

	output wire PHY_RST_N,
	output wire PHY_EN,
	output wire PHY_PWDN,

	output reg  aled_p,
	output wire aled_n,
	output reg  auxled_p,
	output wire auxled_n,

	input  wire aled_in,
	input  wire auxled_in
);

assign PHY_EN   = 1'b1;
assign PHY_PWDN = 1'b1;

phy phy_rx(.*);
phy phy_tx(.*);

assign phy_rx.d   = phy_rx_dat;
assign phy_rx.v   = phy_rx_val;
assign phy_rx.clk = phy_rx_clk;

assign phy_tx_dat = phy_tx.d;
assign phy_tx_val = phy_tx.v;
assign phy_gtx_clk = clk_125m;

udp udp_rx (.*);
udp udp_tx (.*);

eth_vlg #(
	.MAC_ADDR  (48'h1C8AF3FF3EE8),
	.IPV4_ADDR (32'hC0A800d5)
) eth_vlg_inst
(	
	.phy_rx (phy_rx),
	.phy_tx (phy_tx),

	.clk (clk_125m),
	.rst (rst),

	.udp_tx (udp_tx),
	.udp_rx (udp_rx)
);

mdio_master mdio_master_inst (
	.clk       (clk_mdio),
	.rst       (rst),
	.MDIO      (MDIO),
	.MDC       (MDC),
	.PHY_RST_N (PHY_RST_N)
);

endmodule