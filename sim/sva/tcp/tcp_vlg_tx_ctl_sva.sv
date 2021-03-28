import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

`include "../macros.sv"
  
module tcp_vlg_tx_ctl_sva (
  input logic       clk,
  input logic       rst,

  input logic  data_val,
  input logic  data_cts
);

  property val_low_if_cts_low;
    @(posedge clk) disable iff (rst) 
    ($fell(data_cts) |=> $fell(data_val));
  endproperty
 
  ERROR_VAL_HIGH_WHEN_CTS_LOW: assert property (val_low_if_cts_low) 
  else $error("User logic is sending data when TCP cts is low. Possible data lsoss.");
  
endmodule : tcp_vlg_tx_ctl_sva
