module rst_gen #(
  parameter int HOLD_TICKS = 100
)
(
  input  logic clk,
  output logic rst
);
  int ctr;
  initial rst = 1;

  always @ (posedge clk) begin
    ctr <= ctr + 1;
    if (ctr == HOLD_TICKS) rst <= 0;
  end
endmodule : rst_gen
