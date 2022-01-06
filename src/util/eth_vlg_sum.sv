module eth_vlg_sum #(
  parameter int W = 8,
  parameter int N = 4 // 2**N averages
)(
  input  logic                   clk,
  input  logic [2**N-1:0][W-1:0] in,
  output logic [W+N-1:0]         res
);

logic [W+N-2:0] res_a, res_b;

generate
  if (N == 1) begin : trivial
    always @ (posedge clk) res <= in[0] + in[1];
  end
  else begin : inst
    eth_vlg_sum #(.W(W), .N(N-1)) sum_inst_a (.clk(clk), .in(in[2**N-1:2**(N-1)]), .res(res_a));
    eth_vlg_sum #(.W(W), .N(N-1)) sum_inst_b (.clk(clk), .in(in[2**(N-1)-1:0]),    .res(res_b));
    always @ (posedge clk) res <= res_a + res_b;
  end
endgenerate

endmodule : eth_vlg_sum