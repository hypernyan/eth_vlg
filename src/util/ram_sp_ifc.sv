interface ram_sp_ifc
#( 
  parameter AW = 16,
  parameter DW = 16 )
(
);
logic            clk;
logic            rst;
logic [AW - 1:0] a;
logic [DW - 1:0] d;
logic            w;
logic [DW - 1:0] q;

modport mem ( input clk, rst, a, d, w, output q );
modport sys ( input q, output w, a, d );
modport tb  ( output a, d, w, q );

endinterface : ram_sp_ifc
