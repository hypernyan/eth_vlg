// local sequence number tracker 
module tcp_vlg_seq 
  import
    tcp_vlg_pkg::*;
(
  input  logic     clk,
  input  tcb_t     tcb,
  input  logic     init,
  input  logic     val,  
  output tcp_num_t seq
);

  // Sequence number tracker
  always_ff @ (posedge clk) begin
    if (init) seq <= tcb.loc_seq;
    else if (val) seq <= seq + 1;
  end

endmodule : tcp_vlg_seq
