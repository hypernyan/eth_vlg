module buf_mng #(
  parameter               W = 8,   // Width
  parameter               N = 1,   // Number of inputs
  parameter [N-1:0][31:0] D = 7,   // Depth
  parameter bit           RWW = 0  ) // Read While Write
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
endmodule : buf_mng

//`define SIMULATION
module crc32 (
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  d,
  input  logic        v,
  output logic        ok,
  output logic [31:0] crc
);

localparam [31:0] CRC_POLY         = 32'hEDB88320;
localparam [31:0] CRC_MAGIC_NUMBER = 32'hDEBB20E3;
int i, j;
bit [31:0] cur;
int f;

logic [31:0] crc_table [255:0];

initial begin
`ifdef SIMULATION
  f = $fopen("crc_table.txt", "w");
  for (i = 0; i < 256; i = i+1) begin
    cur = i;
  for (j = 0; j < 8; j = j+1) begin
    cur = (cur[0] && 1'b1) ? (cur >> 1) ^ CRC_POLY : cur >> 1; 
    end
    $fwrite(f,"%h\n",cur);
  end
  $fclose(f);
`endif // SIMULATION
  $readmemh("crc_table.txt", crc_table);
end

logic [31:0] crc_del;
logic [31:0] crc_table_q;
logic v_del;

always @ (posedge clk) begin
  if (rst) begin
    v_del       <= 0;
    crc_del     <= 0;
  end
  else begin
    v_del <= v;
    crc_del <= crc;
    crc_table_q <= crc_table[(crc[7:0] ^ d[7:0]) & 8'hff];
  end
end

assign crc = (v_del) ? crc_table_q ^ (crc_del >> 8) : '1; 
assign ok = (crc == CRC_MAGIC_NUMBER);

endmodule : crc32

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

endinterface : fifo_dc_if

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

always @ (posedge fifo.clk_w) begin
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

always @ (posedge fifo.clk_w)
  if (fifo.rst)
    fifo.f_w <= 0;
  else if (fifo.v_w)
    fifo.f_w <= gray_conv (wr_addr + 2) == rd_addr_gray_wr_r;
  else
    fifo.f_w <= fifo.f_w & (gray_conv (wr_addr + 1'b1) == rd_addr_gray_wr_r);

always @ (posedge fifo.clk_w) begin
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

always @ (posedge fifo.clk_w)
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

endmodule : fifo_dc

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

endinterface : fifo_sc_if

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

endmodule : fifo_sc

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

initial for (int i = 0; i < 2**D; i = i + 1) mem[i] = '0;

always @ (posedge clk) if (r_v) r_q <= mem[rd_addr];
always @ (posedge clk) if (w_v) mem[wr_addr] <= w_d;

endmodule : fifo_sc_no_if

module onehot_lsb #(
  parameter WIDTH = 4
)
(
  input wire [WIDTH-1:0] i,
  output reg [WIDTH-1:0] o
);

always @* if (i[0]) o[0] = 1'b1; else o[0] = 1'b0;

genvar idx;
generate
  for (idx = 1; idx < WIDTH; idx = idx + 1) begin : gen always @* if (i[idx] == 1'b1 && i[idx-1:0] == 'b0) o[idx] = 1'b1; else o[idx] = 1'b0; end
endgenerate

endmodule : onehot_lsb

module onehot_msb #(
parameter WIDTH = 4
)
(
  input wire [WIDTH-1:0] i,
  output reg [WIDTH-1:0] o
);

always @* if (i[WIDTH-1] == 1'b1) o[WIDTH-1] = 1'b1; else o[WIDTH-1] = 1'b0;

genvar idx;
generate
  for (idx = WIDTH - 2; idx >= 0; idx = idx - 1) begin : gen always @* if (i[idx] == 1'b1 && i[WIDTH-1:idx+1] == 'b0) o[idx] = 1'b1; else o[idx] = 1'b0; end
endgenerate

endmodule : onehot_msb

interface ram_if
#( 
  parameter ADDR_WIDTH = 16,
  parameter DATA_WIDTH = 16 )
(
  
);
logic clk;
logic rst;
logic [ADDR_WIDTH - 1:0] a_a;
logic [ADDR_WIDTH - 1:0] a_b;
logic [DATA_WIDTH - 1:0] d_a;
logic [DATA_WIDTH - 1:0] d_b;
logic w_a;
logic w_b;
logic [DATA_WIDTH - 1:0] q_a;
logic [DATA_WIDTH - 1:0] q_b;

modport mem ( input clk, rst, w_a, w_b, a_a, a_b, d_a, d_b, output q_a, q_b );
modport sys ( input q_a, q_b, output w_a, w_b, a_a, a_b, d_a, d_b );
modport tb  ( output q_a, q_b, w_a, w_b, a_a, a_b, d_a, d_b );

endinterface : ram_if

interface ram_if_sp
#( 
  parameter ADDR_WIDTH = 16,
  parameter DATA_WIDTH = 16 )
(
  
);

logic                    clk;
logic [ADDR_WIDTH - 1:0] a;
logic [DATA_WIDTH - 1:0] d;
logic                    w;
logic [DATA_WIDTH - 1:0] q;

modport mem ( input clk, a, d, w, output q );
modport sys ( input q, output w, a, d );
modport tb  ( output a, d, w, q );

endinterface : ram_if_sp

module true_dpram_sclk
# ( 
  parameter ADDR_WIDTH = 16,
  parameter DATA_WIDTH = 16 )
(
  ram_if.mem mem_if
);

reg [DATA_WIDTH - 1:0] ram [2**ADDR_WIDTH - 1:0];
initial for (int i = 0; i < 2**ADDR_WIDTH; i = i + 1) ram[i] = '0;

`ifdef SIMULATION
initial begin

  @ ( negedge mem_if.rst )
  @ ( posedge mem_if.clk )
  $readmemh ( "../../src/verilog/true_dpram_sclk/init.txt", ram );
end
`endif

// Port A
always @ ( posedge mem_if.clk ) begin
  if ( mem_if.w_a ) begin
    ram[ mem_if.a_a ] <= mem_if.d_a;
    mem_if.q_a <= mem_if.d_a;
  end
  else mem_if.q_a <= ram[ mem_if.a_a ];
end
// Port B          
always @ ( posedge mem_if.clk ) begin
  if ( mem_if.w_b ) begin
    ram[ mem_if.a_b ] <= mem_if.d_b;
    mem_if.q_b <= mem_if.d_b;
  end
  else mem_if.q_b <= ram[ mem_if.a_b ];
end
  
endmodule : true_dpram_sclk
