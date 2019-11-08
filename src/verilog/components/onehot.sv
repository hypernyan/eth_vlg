module onehot_lsb #(
	parameter WIDTH = 4
)
(
	input wire [WIDTH-1:0] i,
	output reg [WIDTH-1:0] o
);

// Deal with the most significant bit case apart
always @* if (i[0]) o[0] = 1'b1; else o[0] = 1'b0;


// Deal with the rest of bits
genvar idx;

generate
	for (idx = 1; idx < WIDTH; idx = idx + 1) begin : gen always @* if (i[idx] == 1'b1 && i[idx-1:0] == 'b0) o[idx] = 1'b1; else o[idx] = 1'b0; end
endgenerate

endmodule

module onehot_msb #(
parameter WIDTH = 4
)
(
  input wire [WIDTH-1:0] i,
  output reg [WIDTH-1:0] o
);

// Deal with the most significant bit case apart
always @* begin
    if (i[WIDTH-1] == 1'b1)
        o[WIDTH-1] = 1'b1;
    else
        o[WIDTH-1] = 1'b0;
end

// Deal with the rest of bits
genvar idx;

generate
	for (idx = WIDTH - 2; idx >= 0; idx = idx - 1) begin : gen always @* if (i[idx] == 1'b1 && i[WIDTH-1:idx+1] == 'b0) o[idx] = 1'b1; else o[idx] = 1'b0; end
endgenerate

endmodule