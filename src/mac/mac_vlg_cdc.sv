module mac_vlg_cdc #(
  parameter FIFO_DEPTH = 8, // The value should be reasonable for the tool to implement DP RAM
  parameter DELAY = 4 
)(
  input  logic       clk_in,
  input  logic       rst_in,
  input  logic [7:0] data_in,
  input  logic       valid_in,
  input  logic       error_in,

  input  logic       clk_out,
  input  logic       rst_out,
  output logic [7:0] data_out,
  output logic       valid_out,
  output logic       error_out
);

  // Introduce a readout delay to make sure valid_out will have no interruptions 
  // because rx_clk and clk are asynchronous 
  logic [DELAY-1:0] empty;
  fifo_dc_if #(FIFO_DEPTH, 8) fifo(.*);
  fifo_dc    #(FIFO_DEPTH, 8) fifo_inst(.*);
  
  assign fifo.clk_w = clk_in;
  assign fifo.rst_w = rst_in;
  
  assign fifo.data_in = data_in;
  assign fifo.write = valid_in;
  
  assign fifo.clk_r = clk_out;
  assign fifo.rst_r = rst_out;
  
  assign data_out  = fifo.data_out;
  assign valid_out = fifo.valid_out;
  
  always_ff @ (posedge clk_out) begin
    empty[DELAY-1:0] <= {empty[DELAY-2:0], fifo.empty};
    fifo.read <= ~empty[DELAY-1];
  end

endmodule : mac_vlg_cdc
