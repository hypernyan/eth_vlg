module eth_vlg_fifo_dc #(
  parameter ADDR_WIDTH = 3,
  parameter DATA_WIDTH = 32
)
(
  fifo_dc_ifc.fifo fifo
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

always @ (posedge fifo.clk_w or posedge fifo.rst_w) begin
  if (fifo.rst_w) begin
    wr_addr <= 0;
    wr_addr_gray <= 0;
  end else if (fifo.write) begin
    wr_addr <= wr_addr + 1'b1;
    wr_addr_gray <= gray_conv(wr_addr + 1'b1);
  end
end

// synchronize read address to write clock domain
always @ (posedge fifo.clk_w) begin
  rd_addr_gray_wr   <= rd_addr_gray;
  rd_addr_gray_wr_r <= rd_addr_gray_wr;
end

always @ (posedge fifo.clk_w or posedge fifo.rst_w)
  if (fifo.rst_w)
    fifo.full <= 0;
  else if (fifo.write && !fifo.full)
    fifo.full <= gray_conv (wr_addr + 2) == rd_addr_gray_wr_r;
  else
    fifo.full <= fifo.full & (gray_conv (wr_addr + 1'b1) == rd_addr_gray_wr_r);

always @ (posedge fifo.clk_r or posedge fifo.rst_r) begin
  if (fifo.rst_r) begin
    rd_addr      <= 0;
    rd_addr_gray <= 0;
  end else if (fifo.read && !fifo.empty) begin
    rd_addr      <= rd_addr + 1'b1;
    rd_addr_gray <= gray_conv(rd_addr + 1'b1);
  end
end

// synchronize write address to read clock domain
always @ (posedge fifo.clk_r) begin
  wr_addr_gray_rd   <= wr_addr_gray;
  wr_addr_gray_rd_r <= wr_addr_gray_rd;
end

always @ (posedge fifo.clk_r or posedge fifo.rst_r)
  if (fifo.rst_r)
    fifo.empty <= 1'b1;
  else if (fifo.read && !fifo.empty)
    fifo.empty <= gray_conv (rd_addr + 1) == wr_addr_gray_rd_r;
  else
    fifo.empty <= fifo.empty & (gray_conv (rd_addr) == wr_addr_gray_rd_r);

// generate dual clocked memory
reg [DATA_WIDTH-1:0] mem[(1<<ADDR_WIDTH)-1:0];

always @(posedge fifo.clk_r) begin
  if (fifo.read && !fifo.empty) fifo.data_out <= mem[rd_addr];
  fifo.valid_out <= (fifo.read && !fifo.empty);
end
always @(posedge fifo.clk_w) if (fifo.write && !fifo.full) mem[wr_addr] <= fifo.data_in;

endmodule : eth_vlg_fifo_dc
