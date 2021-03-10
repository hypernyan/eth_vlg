import eth_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;

`define assert_clk(arg) \
  assert property (@(posedge clk) disable iff (rst) arg)


module mac_vlg_rx_asrt (
  input logic clk,
  input logic rst,
  phy.in      phy,
  mac.in_rx   mac,
  input dev_t dev
);

ERROR_SOF_SHOULD_BE_FIRST :
  `assert_clk (mac.sof && !mac.val && ($past(mac.val)));
endproperty

endmodule : mac_vlg_rx_asrt
