interface phy_ifc;
  logic       clk;
  logic       rst;
  logic [7:0] dat;
  logic       val;
  logic       err;
  
  modport in  (input  clk, rst, dat, val, err);
  modport out (output clk, rst, dat, val, err);
  modport sva (input  clk, rst, dat, val, err);
endinterface : phy_ifc
