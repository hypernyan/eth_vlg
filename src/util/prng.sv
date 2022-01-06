`ifndef MODULE_PRNG
`define MODULE_PRNG

module prng #(
  parameter int W = 32,
  //                           32      24      16      8       0
  //                           |       |       |       |       |
  parameter [W-1:0] POLY = 32'b10000000001000000000000000000011,
  parameter [W-1:0] SEED = 32'hdeadbeef
)(
  input  logic         clk,
  input  logic         rst,
  input  logic         in,
  output logic [W-1:0] res
);

always @ (posedge clk) if (rst) res <= SEED; else res <= (res[0]) ? {in, res[(W-1):1]} ^ POLY : {in, res[(W-1):1]};

endmodule : prng
`endif // MODULE_PRNG
