`timescale 1 ns / 1 ps

module mdio_tb ();
reg clk = 0;
reg rst = 1;



wire MDIO;
wire MDC; 
wire MDO; 
wire MDT; 
wire MDI;

wire        PHY_RST_N;


initial begin
	#1000 rst <= 0;	
end

mdio_master dut (
	clk,
	rst,

	MDIO,
	MDC, 
	MDO, 
	MDT, 
	MDI,

	PHY_RST_N

);

always #5 clk <= !clk;
endmodule