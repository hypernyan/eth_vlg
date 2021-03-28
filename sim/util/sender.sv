`include "clkdef.sv"
module sender (
  input  logic clk,
  input  logic rst,

  output byte  dout,
  output logic vout,
  input  logic cts,

  input  byte  data[$],
  input  bit   val
);

  byte cur[$];

  always @ (posedge clk) begin
    if (val && $size(data)) begin
      cur = new[$size(data)](data);
    end
    else if (cts && $size(cur)) begin
      dout <= cur.pop_front();
      vout <= 1;
    end
    else vout <= 0;
  end

endmodule : sender