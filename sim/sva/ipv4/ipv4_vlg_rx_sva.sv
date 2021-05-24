import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

`include "../macros.sv"
  
module ipv4_vlg_rx_sva (
  input logic clk,
  input logic rst,
  input dev_t dev,

  mac.sva     mac,
  ipv4.sva    ipv4
);

  property sof_one_tick;
    @(posedge clk) disable iff (rst) 
    (ipv4.strm.sof |-> $past(!ipv4.strm.sof));
  endproperty
 
  property sof_with_val;
    @(posedge clk) disable iff (rst) 
    (ipv4.strm.sof |-> ipv4.strm.val);
  endproperty
 
  property sof_first;
    @(posedge clk) disable iff (rst) 
    (ipv4.strm.sof |-> !($past(ipv4.strm.val)));
  endproperty
 
  property eof_one_tick;
    @(posedge clk) disable iff (rst) 
    (ipv4.strm.eof |-> $past(!ipv4.strm.eof));
  endproperty
 
  property eof_with_val;
    @(posedge clk) disable iff (rst) 
    (ipv4.strm.eof |-> ipv4.strm.val);
  endproperty
 
  property eof_last;
    @(posedge clk) disable iff (rst) 
    (($past(ipv4.strm.eof) && $past(ipv4.strm.val)) |-> !ipv4.strm.val);
  endproperty
 
  property bad_length;
    @(posedge clk) disable iff (rst) 
    (ipv4.strm.sof |-> ##48 !ipv4.strm.val);
  endproperty
 
  ERROR_SOF_LENGTH: assert property (sof_one_tick) else $error("SOF was high more then 1 tick");
  ERROR_SOF_VAL:    assert property (sof_with_val) else $error("SOF was high when VAL was low");
  ERROR_SOF_FIRST:  assert property (sof_first)    else $error("SOF did not appear for 1st byte");
 
  ERROR_EOF_LENGTH: assert property (eof_one_tick) else $error("EOF was high more then 1 tick");
  ERROR_EOF_VAL:    assert property (eof_with_val) else $error("EOF was high when VAL was low");
  ERROR_EOF_LAST:   assert property (eof_last)     else $error("EOF did not appear for last byte");
  
endmodule : ipv4_vlg_rx_sva
