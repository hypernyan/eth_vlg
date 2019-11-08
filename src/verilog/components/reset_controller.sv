module reset_controller (
	input wire clk_25m,
	input wire phy_rx_clk,
	input wire ext_rst,  // external async reset
	output wire eth_rx_latch_clk,
	output wire arst_rx_n,

	output wire clk_125m,
	output wire clk_125m_shift,
	output wire clk_10m,
	output reg  rst_n = 0,   // syncronized reset for 125 and 10 MHz clocks
	output wire rst,
	output wire arst
);

reg [15:0] counter;
//assign clk_125m = clk_25m;
logic_pll logic_pll_inst(
	.refclk   ( clk_25m ),
	.rst      ( ext_rst ),
	.outclk_0 ( clk_125m ),
	.outclk_1 ( clk_125m_shift ),
	.outclk_2 ( clk_10m ),
	.outclk_3 ( clk_50m ),
	.locked   ( arst_n )
);

//pll pll_inst (
//	.areset ( ext_rst ),
//	.inclk0 ( clk_25m ),
//	.c0     ( clk_125m ),
//	.c1     ( clk_10m ),
//	.locked ( arst_n )
//);

wire arst_n; 
assign arst = !arst_n; 
reg rsta_n; // ff for handling metastability
reg rsta_50_n; // ff for handling metastability

// reset sync using the slowest clock
reg rst_n_125;
reg rst_n_50;

always_ff @ ( posedge clk_125m or negedge arst_n ) begin
	if ( !arst_n ) { rst_n_125, rsta_n } <= 2'b00;
	else           { rst_n_125, rsta_n } <= { rsta_n, 1'b1 };
end

always_ff @ ( posedge clk_125m ) begin
	rst_n <= rst_n_125;
end
/*
always_ff @ ( posedge clk_50m or negedge arst_n ) begin
	if ( !arst_n ) { rst_n_50, rsta_50_n } <= 2'b00;
	else           { rst_n_50, rsta_50_n } <= { rsta_50_n, 1'b1 };
end

always_ff @ ( posedge clk_50m ) begin
	rst_n <= rst_n_50;
end
*/
assign rst = !rst_n;
assign rst_50m = !rst_n;


endmodule