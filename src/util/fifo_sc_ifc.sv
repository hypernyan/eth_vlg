interface fifo_sc_ifc
#( 
  parameter D = 16,
  parameter W = 16 )
();
  logic         rst;
  logic         clk;
  
  logic         write;
  logic [W-1:0] data_in;
  
  logic         read;
  logic [W-1:0] data_out;
  logic         valid_out;
  
  logic         full;
  logic         empty;
  
  modport fifo (input rst, clk, write, data_in, read, output data_out, valid_out, full, empty);
  modport sys  (input data_out, valid_out, full, empty, output rst, clk, write, data_in, read);
  modport tb   (output data_out, valid_out, full, empty, rst, clk, write, data_in, read);

endinterface : fifo_sc_ifc
