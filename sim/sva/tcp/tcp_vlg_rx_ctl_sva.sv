import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

`include "../macros.sv"
  
module tcp_vlg_rx_ctl_sva (
  input logic      clk,
  input logic      rst,

  input dev_t      dev,

  rx_ctl.sva       ctl
);

 //property rx_seq_is_in_order;
 //  @(posedge clk) disable iff (rst) 
 // // (meta.val && pld_len != 0 |-> meta.tcp_seq == loc_ack);
 //endproperty
 //
 //INFO_TCP_OUT_OF_ORDER : assert property (rx_seq_is_in) 
 //else $info("TCP out-of-order!");
  
endmodule : tcp_vlg_rx_ctl_sva
