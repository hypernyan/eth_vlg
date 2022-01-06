interface ram_req #(
  parameter AW = 16,
  parameter DW = 16
);
  logic           r_nw;
  logic           v_in;
  logic [AW-1:0]  a_in;
  logic [DW-1:0]  d_in;
  
  logic [AW-1:0] v_out;
  logic [DW-1:0] a_out;
  logic          d_out;
  modport mem (input r_nw, v_in, a_in, d_in, output v_out, a_out, d_out);
  modport sys (output r_nw, v_in, a_in, d_in, input v_out, a_out, d_out);
endinterface : ram_req
