interface ram_dp_ifc
#( 
  parameter AW = 16,
  parameter DW = 16 )
(
);
logic clk_a;
logic clk_b;
logic rst;
logic [AW - 1:0] a_a;
logic [AW - 1:0] a_b;
logic [DW - 1:0] d_a;
logic [DW - 1:0] d_b;
logic w_a;
logic w_b;
logic [DW - 1:0] q_a;
logic [DW - 1:0] q_b;

modport mem ( input clk_a, clk_b, rst, w_a, w_b, a_a, a_b, d_a, d_b, output q_a, q_b );
modport sys ( input q_a, q_b, output w_a, w_b, a_a, a_b, d_a, d_b );
modport tb  ( output q_a, q_b, w_a, w_b, a_a, a_b, d_a, d_b );

endinterface : ram_dp_ifc
