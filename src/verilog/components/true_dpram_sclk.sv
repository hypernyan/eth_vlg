//`define SIMULATION
interface ram_if
#( 
	parameter ADDR_WIDTH = 16,
	parameter DATA_WIDTH = 16 )
(
	
);
logic clk;
logic rst;
logic [ADDR_WIDTH - 1:0] a_a;
logic [ADDR_WIDTH - 1:0] a_b;
logic [DATA_WIDTH - 1:0] d_a;
logic [DATA_WIDTH - 1:0] d_b;
logic w_a;
logic w_b;
logic [DATA_WIDTH - 1:0] q_a;
logic [DATA_WIDTH - 1:0] q_b;

modport mem ( input clk, rst, w_a, w_b, a_a, a_b, d_a, d_b, output q_a, q_b );
modport sys ( input q_a, q_b, output w_a, w_b, a_a, a_b, d_a, d_b );
modport tb  ( output q_a, q_b, w_a, w_b, a_a, a_b, d_a, d_b );

endinterface

interface ram_if_sp
#( 
	parameter ADDR_WIDTH = 16,
	parameter DATA_WIDTH = 16 )
(
	
);

logic                    clk;
logic [ADDR_WIDTH - 1:0] a;
logic [DATA_WIDTH - 1:0] d;
logic                    w;
logic [DATA_WIDTH - 1:0] q;

modport mem ( input clk, a, d, w, output q );
modport sys ( input q, output w, a, d );
modport tb  ( output a, d, w, q );

endinterface

module true_dpram_sclk
# ( 
	parameter ADDR_WIDTH = 16,
	parameter DATA_WIDTH = 16 )
(
	ram_if.mem mem_if
);

reg [DATA_WIDTH - 1:0] ram [2**ADDR_WIDTH - 1:0];
initial for (int i = 0; i < 2**ADDR_WIDTH; i = i + 1) ram[i] = '0;

`ifdef SIMULATION
initial begin

  @ ( negedge mem_if.rst )
  @ ( posedge mem_if.clk )
  $readmemh ( "../../src/verilog/true_dpram_sclk/init.txt", ram );
end
`endif

	// Port A
	always @ ( posedge mem_if.clk ) begin
		if ( mem_if.w_a ) begin
			ram[ mem_if.a_a ] <= mem_if.d_a;
			mem_if.q_a <= mem_if.d_a;
		end
		else mem_if.q_a <= ram[ mem_if.a_a ];
	end
	// Port B          
	always @ ( posedge mem_if.clk ) begin
		if ( mem_if.w_b ) begin
			ram[ mem_if.a_b ] <= mem_if.d_b;
			mem_if.q_b <= mem_if.d_b;
		end
		else mem_if.q_b <= ram[ mem_if.a_b ];
	end
	
endmodule