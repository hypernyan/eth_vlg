module eth_switch_sim #(
  parameter int N = 3,
  parameter int D = 12,
  parameter int IFG = 10

)(
  input logic clk,
  input logic rst,

  input logic [7:0][N-1:0] din,
  input logic      [N-1:0] vin,

  output logic [7:0][N-1:0] dout,
  output logic      [N-1:0] vout
);

logic rdy;
logic [N-1:0]       act_ms;
logic [N-1:0]       fifo_r;
logic [N-1:0] [7:0] fifo_o;
logic [N-1:0]       fifo_v;
logic [N-1:0]       fifo_e;
logic [N-1:0]       fifo_f;
logic [N-1:0]       cur;
logic [N-1:0]       avl_v;

wor [$clog2(N+1)-1:0] ind;

assign rdy = 1;

genvar i;

generate
  for (i = 0; i < N; i = i + 1) begin : gen
    fifo_sc_no_if #(D, 8) fifo_inst (
      .rst      (rst),
      .clk      (clk),
      .write    (vin[i] && !fifo_f[i]),
      .data_in  (din[i]),

      .read      (fifo_r[i] && !fifo_e[i]),
      .data_out  (fifo_o[i]),
      .valid_out (fifo_v[i]),

      .full     (fifo_f[i]),
      .empty    (fifo_e[i])
    );
    always @ (posedge clk) if (rst || ifg_ctr != 0) cur[i] <= 0; else cur[i] <= (rdy) ? ((!fifo_e[i] && fifo_r[i]) || act_ms[i]) : (cur[i] && !fifo_e[i]);
    assign ind = (fifo_r[i] == 1'b1) ? i : 0;
    always @ (posedge clk) if (rst) avl_v[i] <= 0; else avl_v[i] <= ~fifo_e[i]; // fifo is available to read if it is not empty
    assign dout[i] = fifo_o[ind];
    assign vout[i] = fifo_v[ind];
  end
endgenerate

always @ (posedge clk) begin
  if (rst) ifg_ctr <= 0;
  else if (vout) ifg_ctr <= IFG;
  else ifg_ctr <= (ifg_ctr == 0) ? 0 : ifg_ctr - 1;
end

onehot #(N, 1) onehot_msb_inst (
  .i (avl_v),
  .o (act_ms)
);

onehot #(N, 0) onehot_lsb_inst (
  .i (cur),
  .o (fifo_r)
);

endmodule