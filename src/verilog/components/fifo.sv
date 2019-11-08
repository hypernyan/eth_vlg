interface fifo_dc_if
#(
	parameter ADDR_WIDTH = 16,
	parameter DATA_WIDTH = 16)
();

	logic                  rst;
	logic                  clk_w;
	logic                  clk_r;
	
	logic                  v_w;
	logic [DATA_WIDTH-1:0] d_w;
	
	logic                  v_r;
	logic [DATA_WIDTH-1:0] q_r;
	
	logic                  f_w;
	logic                  e_r;
	
	modport fifo (input rst, clk_w, clk_r, v_w, d_w, v_r, output q_r, f_w, e_r);
	modport sys  (input q_r, f_w, e_r, output rst, clk_w, clk_r, v_w, d_w, v_r);

endinterface


module fifo_dc #(
	parameter ADDR_WIDTH = 3,
	parameter DATA_WIDTH = 32
)
(
	fifo_dc_if.fifo fifo
);

reg [ADDR_WIDTH-1:0] wr_addr;
reg [ADDR_WIDTH-1:0] wr_addr_gray;
reg [ADDR_WIDTH-1:0] wr_addr_gray_rd;
reg [ADDR_WIDTH-1:0] wr_addr_gray_rd_r;
reg [ADDR_WIDTH-1:0] rd_addr;
reg [ADDR_WIDTH-1:0] rd_addr_gray;
reg [ADDR_WIDTH-1:0] rd_addr_gray_wr;
reg [ADDR_WIDTH-1:0] rd_addr_gray_wr_r;

function [ADDR_WIDTH-1:0] gray_conv;
	input [ADDR_WIDTH-1:0] in;
	begin
		gray_conv = {in[ADDR_WIDTH-1], in[ADDR_WIDTH-2:0] ^ in[ADDR_WIDTH-1:1]};
	end
endfunction

always @ (posedge fifo.clk_w or posedge fifo.rst) begin
	if (fifo.rst) begin
		wr_addr <= 0;
		wr_addr_gray <= 0;
	end else if (fifo.v_w) begin
		wr_addr <= wr_addr + 1'b1;
		wr_addr_gray <= gray_conv(wr_addr + 1'b1);
	end
end

// synchronize read address to write clock domain
always @ (posedge fifo.clk_w) begin
	rd_addr_gray_wr   <= rd_addr_gray;
	rd_addr_gray_wr_r <= rd_addr_gray_wr;
end

always @ (posedge fifo.clk_w or posedge fifo.rst)
	if (fifo.rst)
		fifo.f_w <= 0;
	else if (fifo.v_w)
		fifo.f_w <= gray_conv (wr_addr + 2) == rd_addr_gray_wr_r;
	else
		fifo.f_w <= fifo.f_w & (gray_conv (wr_addr + 1'b1) == rd_addr_gray_wr_r);

always @ (posedge fifo.clk_w or posedge fifo.rst) begin
	if (fifo.rst) begin
		rd_addr      <= 0;
		rd_addr_gray <= 0;
	end else if (fifo.v_r) begin
		rd_addr      <= rd_addr + 1'b1;
		rd_addr_gray <= gray_conv(rd_addr + 1'b1);
	end
end

// synchronize write address to read clock domain
always @ (posedge fifo.clk_r) begin
	wr_addr_gray_rd   <= wr_addr_gray;
	wr_addr_gray_rd_r <= wr_addr_gray_rd;
end

always @ (posedge fifo.clk_w or posedge fifo.rst)
	if (fifo.rst)
		fifo.e_r <= 1'b1;
	else if (fifo.v_r)
		fifo.e_r <= gray_conv (rd_addr + 1) == wr_addr_gray_rd_r;
	else
		fifo.e_r <= fifo.e_r & (gray_conv (rd_addr) == wr_addr_gray_rd_r);

// generate dual clocked memory
reg [DATA_WIDTH-1:0] mem[(1<<ADDR_WIDTH)-1:0];

always @(posedge fifo.clk_r) if (fifo.v_r) fifo.q_r <= mem[rd_addr];

always @(posedge fifo.clk_w) if (fifo.v_w) mem[wr_addr] <= fifo.d_w;
endmodule

interface fifo_sc_if
#( 
	parameter D = 16,
	parameter W = 16 )
();
	logic         rst;
	logic         clk;
	
	logic         w_v;
	logic [W-1:0] w_d;
	
	logic         r_v;
	logic [W-1:0] r_q;
	
	logic         f;
	logic         e;
	
	modport fifo (input rst, clk, w_v, w_d, r_v, output r_q, f, e);
	modport sys  (input r_q, f, e, output rst, clk, w_v, w_d, r_v);
	modport tb   (output r_q, f, e, rst, clk, w_v, w_d, r_v);

endinterface

module fifo_sc #(
	parameter D = 16,
	parameter W = 16
)
(
	fifo_sc_if.fifo fifo
);

logic [D-1:0] wr_addr;
logic [D-1:0] rd_addr;
logic [D:0]   diff;
logic [D:0]   wr_ctr;
logic [D:0]   rd_ctr;

assign diff = wr_ctr - rd_ctr;

assign fifo.e = (diff == 0);
assign fifo.f = (diff[D] == 1);

always @ (posedge fifo.clk) begin
	if (fifo.rst) wr_ctr <= 0;
	else if (fifo.w_v && !fifo.f) wr_ctr <= wr_ctr + 1;
end

assign wr_addr[D-1:0] = wr_ctr[D-1:0];
assign rd_addr[D-1:0] = rd_ctr[D-1:0];

always @ (posedge fifo.clk) begin
	if (fifo.rst) rd_ctr <= 0;
	else if (fifo.r_v && !fifo.e) rd_ctr <= rd_ctr + 1;
end

reg [W-1:0] mem[(1<<D)-1:0];

int i;

initial for (i = 0; i < 2**D; i = i + 1) mem[i] = '0;

always @ (posedge fifo.clk) if (fifo.r_v) fifo.r_q <= mem[rd_addr];

always @ (posedge fifo.clk) if (fifo.w_v) mem[wr_addr] <= fifo.w_d;

endmodule

module fifo_sc_no_if #(
	parameter D = 16,
	parameter W = 16
)
(
	input  logic         rst,
	input  logic         clk,
	
	input  logic         w_v,
	input  logic [W-1:0] w_d,
	
	input  logic         r_v,
	output logic [W-1:0] r_q,
	
	output logic         f,
	output logic         e
);

logic [D-1:0] wr_addr;
logic [D-1:0] rd_addr;
logic [D:0]   diff;
logic [D:0]   wr_ctr;
logic [D:0]   rd_ctr;

assign diff = wr_ctr - rd_ctr;

assign e = (diff == 0);
assign f = (diff[D] == 1);

always @ (posedge clk) begin
	if (rst) wr_ctr <= 0;
	else if (w_v && !f) wr_ctr <= wr_ctr + 1;
end

assign wr_addr[D-1:0] = wr_ctr[D-1:0];
assign rd_addr[D-1:0] = rd_ctr[D-1:0];

always @ (posedge clk) begin
	if (rst) rd_ctr <= 0;
	else if (r_v && !e) rd_ctr <= rd_ctr + 1;
end

reg [W-1:0] mem[(1<<D)-1:0];

int i;

initial for (i = 0; i < 2**D; i = i + 1) mem[i] = '0;

always @ (posedge clk) if (r_v) r_q <= mem[rd_addr];

always @ (posedge clk) if (w_v) mem[wr_addr] <= w_d;

endmodule
