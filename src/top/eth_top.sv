
module tcp_cyclonev (
	input wire  clk_25m,
	// 
	// ETH
	// 
	output wire       phy_gtx_clk,
	input  wire       phy_rx_clk, 

	output wire       phy_tx_err, 
	output wire       phy_tx_val, 
	output wire [7:0] phy_tx_dat, 

	input  wire       phy_rx_err, 
	input  wire       phy_rx_val,
	input  wire [7:0] phy_rx_dat,

	input  wire       phy_crs, // half-duplex only
	input  wire       phy_col, // half-duplex only

	output wire       MDC,
	output wire       MDIO,

	output wire       PHY_RST_N,
	output wire       PHY_EN,
	output wire       PHY_PWDN,

	input  wire       aled_in,
	input  wire       auxled_in,

	output wire       aled_n,
	output wire       aled_p,
	output wire       auxled_n,
	output wire       auxled_p,

	output wire       LED
);

reset_controller reset_controller_inst (
	.clk_25m          (clk_25m),
	.phy_rx_clk       (phy_rx_clk),
	.ext_rst          (0),  // external async reset
	.eth_rx_latch_clk (eth_rx_latch_clk),
	.arst_rx_n        (arst_rx_n),
	.clk_125m         (clk_125m),
	.clk_125m_shift   (clk_125m_shift),
	.clk_10m          (clk_10m),
	.rst_n            (rst_n),
	.rst              (rst),
	.arst             (arst)
);

ethernet ethernet_inst (
	.phy_rx_clk     (phy_rx_clk),
	.phy_gtx_clk    (phy_gtx_clk),
	.clk_125m       (phy_rx_clk),
	.clk_mdio       (clk_10m),

	.rst           (rst),
	.arst          (arst),

	.phy_rx_dat    (phy_rx_dat),
	.phy_rx_val    (phy_rx_val),
	.phy_rx_err    (phy_rx_err),

	.phy_tx_dat    (phy_tx_dat),
	.phy_tx_val    (phy_tx_val),
	.phy_tx_err    (phy_tx_err),

	.MDIO          (MDIO),      
	.MDC           (MDC),       
	.PHY_RST_N     (PHY_RST_N),

	.PHY_EN    (PHY_EN   ),
	.PHY_PWDN  (PHY_PWDN ), 

	.aled_p    (aled_p   ),
	.auxled_p  (auxled_p ),

	.aled_in   (aled_in  ),
	.auxled_in (auxled_in)
);

endmodule
