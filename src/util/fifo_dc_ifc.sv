interface fifo_dc_ifc
#(
  parameter W = 16,
  parameter D = 16
)
();

  logic         rst_w;
  logic         rst_r;
  logic         clk_w;
  logic         clk_r;
  
  logic         write;
  logic [D-1:0] data_in;
  
  logic         read;
  logic [D-1:0] data_out;
  logic         valid_out;
  
  logic         full;
  logic         empty;
  
  modport fifo (input rst_w, rst_r, clk_w, clk_r, write, data_in, read, output data_out, valid_out, full, empty);
  modport sys  (input data_out, valid_out, full, empty, output rst_w, rst_r, clk_w, clk_r, write, data_in, read);

endinterface : fifo_dc_ifc
