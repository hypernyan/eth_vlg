`timescale 1 ns / 1 ps

module mdio_master ( 

	input  wire clk,
	input  wire rst,

	inout  wire MDIO,
	output wire MDC,
	output wire MDO, 
	output wire MDT, 
	output wire MDI,

	output reg  PHY_RST_N

);
// Parameters
parameter PHY_ADDR = 2'b00;
parameter MDIO_PAUSE = 1000;

// Regs'n'wires 
reg         config_start;
reg  [31:0] mdio_rom_q;
reg  [15:0] reset_counter;
reg         phy_rdwr;
wire        phy_ack;
wire [15:0] phy_rdat;
reg  [15:0] phy_tdat;
reg         count_en;
reg  [3:0]  prg_ctr;
reg  [6:0]  phy_raddr;
reg         phy_strt;
reg         cont;
reg  [10:0] pause_ctr;
reg         start_pause;
reg         start;
wire        MDCtri;

// Tri-state control
//                   TX       RX
assign MDIO = MDT ? MDO    : 1'b1;
assign MDI  = MDT ? 1'b0   : MDIO;
assign MDC  = MDT ? MDCtri : 1'b1;


nf2_mdio nf2_mdio_inst (
	.phy_reg_req     ( phy_strt  ),
	.phy_reg_rd_wr_L ( phy_rdwr  ),
	.phy_reg_ack     ( phy_ack   ),
	.phy_reg_addr    ( phy_raddr ),
	.phy_reg_rd_data ( phy_rdat  ),
	.phy_reg_wr_data ( phy_tdat  ),
	
   // --- pin outputs (and tri-enable)

	.phy_mdc         ( MDCtri ),
	.phy_mdata_out   ( MDO ),
	.phy_mdata_tri   ( MDT ),
	.phy_mdata_in    ( MDI ),

   // --- Misc

	.reset           ( rst ),
	.clk             ( clk )
);

always @ ( posedge clk ) begin
	if ( rst ) begin
		reset_counter <= 16'h0000;
		PHY_RST_N <= 1'b0;
		count_en <= 1'b1;
		config_start <= 1'b0;
	end
	else if ( count_en ) begin
		reset_counter <= reset_counter + 1;
		if ( reset_counter == 16'h7000 ) begin
			PHY_RST_N <= 1'b1;
		end
		if ( reset_counter == 16'hffff ) begin
			count_en <= 1'b0;
			config_start <= 1'b1;
		end
	end
end
reg [31:0] mdio_dat;
reg [31:0] mdio_rom [0:8] = '{
	32'h0000_1200, // auto-negotiation enable, restart auto-negotiation 
	
	32'h000D_001F, // extended address access, set pointer mode
	32'h000E_0032, // set pounter to 0x0032 ( RGMII Control Register )
	32'h000D_401F, // extended address access, set write data mode
	32'h000E_0000, // write 0 to 0x0032
	
	32'h000D_001F, // 
	32'h000E_0031, // CFG4 - Configuration Register 4
	32'h000D_401F, // 
	32'h000E_0080  // Normal Operation
};

always @ ( posedge clk ) begin
	mdio_dat <= mdio_rom[prg_ctr];
end

always @ ( posedge clk ) begin
	if ( !config_start ) begin
		prg_ctr   <= 0;
		start     <= 1;
		phy_strt  <= 0;
		pause_ctr <= 0;
		cont      <= 0;
		phy_tdat  <= 0;
	end
	else begin
		phy_tdat[15:0] <= mdio_dat[15:0];
		phy_raddr[4:0] <= mdio_dat[20:16];
		phy_raddr[6:5] <= PHY_ADDR;
		if ( ( cont | start ) & prg_ctr != 9 ) begin
			start          <= 0;
			cont           <= 0;
			phy_strt       <= 1;
			phy_rdwr       <= 1'b0; // write opcode
		end
		else begin
			phy_strt <= 0; // keep phy_start '0' until continue, start or end of program are detected
		end
		if ( phy_ack ) begin  // when PHY acknowledges: 
			start_pause <= 1; // start a pause
		end
		if ( start_pause ) begin
			pause_ctr <= pause_ctr + 1;
			if ( pause_ctr == 0 ) begin
				prg_ctr        <= prg_ctr + 1;   // increment rom addr,
			end
			if ( pause_ctr == MDIO_PAUSE ) begin // when pause counter counts to MDIO_PAUSE: 
				pause_ctr <= 0;                  // reset pause counter,
				start_pause <= 0;                // deassert start_pause
				cont <= 1;                       // set continue to '1'
			end
		end
	end
end

endmodule