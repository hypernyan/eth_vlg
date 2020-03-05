module buf_mng #(
  parameter               W = 8,   // Width
  parameter               N = 1,   // Number of inputs
  parameter [N-1:0][31:0] D = 7,   // Depth
  parameter bit         RWW = 0  ) // Read While Write
(
	input  logic clk,
	input  logic rst,

	input  logic [N-1:0]         rst_fifo,
	input  logic [N-1:0]         v_i,
	input  logic [N-1:0] [W-1:0] d_i,

	output logic         v_o,
	output logic [W-1:0] d_o,
	output logic         eof,

	input  logic         rdy,
	output logic         avl,
	output logic [N-1:0] act_ms
);

logic [N-1:0]         fifo_r;
logic [N-1:0] [W-1:0] fifo_o;
logic [N-1:0]         fifo_e;
logic [N-1:0]         fifo_f;

logic [N-1:0] cur;

 wor   [$clog2(N+1)-1:0] ind;
//wire [$clog2(N+1)-1:0] ind;
logic [N-1:0] avl_v;

assign avl = (avl_v != 0);

genvar i;

generate
	for (i = 0; i < N; i = i + 1) begin : gen
		fifo_sc_no_if  #(D[i], W) fifo_inst (
			.rst  (rst_fifo[i] || rst),
			.clk  (clk),
			.w_v  (v_i[i] && !fifo_f[i]),
			.w_d  (d_i[i]),

			.r_v  (fifo_r[i] && !fifo_e[i]),
			.r_q  (fifo_o[i]),

			.f    (fifo_f[i]),
			.e    (fifo_e[i])
		);
		always @ (posedge clk) if (rst) cur[i] <= 0; else cur[i] <= (rdy) ? ((!fifo_e[i] && fifo_r[i]) || act_ms[i]) : (cur[i] && !fifo_e[i]);
		assign ind = (fifo_r[i] == 1'b1) ? i : 0;
		always @ (posedge clk) if (rst_fifo[i]) avl_v[i] <= 0; else avl_v[i] <= (~fifo_e[i] && (~v_i[i] || RWW)); // fifo is available to read if it is not empty
	end
endgenerate

onehot_msb #(N) onehot_msb_inst (
	.i (avl_v),
	.o (act_ms)
);

onehot_lsb #(N) onehot_lsb_inst (
	.i (cur),
	.o (fifo_r)
);

assign d_o = fifo_o [ind][W-1:0];

always @ (posedge clk) v_o <= (fifo_r && !fifo_e[ind]);
assign eof = v_o && fifo_e[ind];
endmodule
