module eth_vlg_buf #(
	parameter BUF_SIZE = 10
)
(
	input logic clk,
	input logic rst,
	input logic [7:0] buf_d,
	input logic [BUF_SIZE-1:0] buf_a_w,
	input logic [BUF_SIZE-1:0] buf_a_r,
	input logic buf_v,
	output logic [7:0] buf_q
);

reg [7:0] mem[(1<<BUF_SIZE)-1:0];

always @ (posedge clk) if (buf_v) mem[buf_a_w] <= buf_d;
always @ (posedge clk) buf_q <= mem[buf_a_r];

endmodule
