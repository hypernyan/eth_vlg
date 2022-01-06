module eth_vlg_fifo_sc #(
  parameter D = 16,
  parameter W = 16
)
(
  fifo_sc_ifc.fifo fifo
);

logic [D-1:0] wr_addr;
logic [D-1:0] rd_addr;
logic [D:0]   diff;
logic [D:0]   wr_ctr;
logic [D:0]   rd_ctr;

assign diff = wr_ctr - rd_ctr;

assign fifo.empty = (diff == 0);
assign fifo.full = (diff[D] == 1);

always @ (posedge fifo.clk) begin
  if (fifo.rst) wr_ctr <= 0;
  else if (fifo.write && !fifo.full) wr_ctr <= wr_ctr + 1;
end

assign wr_addr[D-1:0] = wr_ctr[D-1:0];
assign rd_addr[D-1:0] = rd_ctr[D-1:0];

always @ (posedge fifo.clk) begin
  if (fifo.rst) rd_ctr <= 0;
  else if (fifo.read && !fifo.empty) rd_ctr <= rd_ctr + 1;
end

reg [W-1:0] mem[(1<<D)-1:0];

int i;

initial for (i = 0; i < 2**D; i = i + 1) mem[i] = '0;

always @ (posedge fifo.clk) begin
  if (fifo.read && !fifo.empty) fifo.data_out <= mem[rd_addr];
  fifo.valid_out <= (fifo.read && !fifo.empty);
  if (fifo.write && !fifo.full) mem[wr_addr] <= fifo.data_in;
end

endmodule : eth_vlg_fifo_sc
