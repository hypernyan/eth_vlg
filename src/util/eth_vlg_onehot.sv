module eth_vlg_onehot #(
	parameter int W = 4,
	parameter bit MSB = 1
)
(
	input wire [W-1:0] i,
	output reg [W-1:0] o
);

// Deal with the most significant bit case apart


// Deal with the rest of bits
genvar idx;

generate
  if (MSB) begin : gen_lsb
	  for (idx = W - 2; idx >= 0; idx = idx - 1) begin : gen always @* if (i[idx] == 1'b1 && i[W-1:idx+1] == 'b0) o[idx] = 1'b1; else o[idx] = 1'b0; end
    always @* if (i[W-1]) o[W-1] = 1'b1; else o[W-1] = 1'b0;
  end
  else begin : gen_msb
	for (idx = 1; idx < W; idx = idx + 1) begin : gen always @* if (i[idx] == 1'b1 && i[idx-1:0] == 'b0) o[idx] = 1'b1; else o[idx] = 1'b0; end
    always @* if (i[0]) o[0] = 1'b1; else o[0] = 1'b0;
  end
endgenerate

endmodule : eth_vlg_onehot

