import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

`include "../macros.sv"
  
module mac_vlg_rx_sva (
  input logic       clk,
  input logic       rst,

  input stream_t    strm,
  input mac_meta_t  meta,
  input logic       phy_clk,
  input logic       phy_rst,
  input logic [7:0] phy_dat,
  input logic       phy_val,
  input logic       phy_err,
  input dev_t       dev
);

  property sof_one_tick;
    @(posedge clk) disable iff (rst) 
    (strm.sof |-> $past(!strm.sof));
  endproperty
 
  property sof_with_val;
    @(posedge clk) disable iff (rst) 
    (strm.sof |-> strm.val);
  endproperty
 
  property sof_first;
    @(posedge clk) disable iff (rst) 
    (strm.sof |-> !($past(strm.val)));
  endproperty
 
  property eof_one_tick;
    @(posedge clk) disable iff (rst) 
    (strm.eof |-> $past(!strm.eof));
  endproperty
 
  property eof_with_val;
    @(posedge clk) disable iff (rst) 
    (strm.eof |-> strm.val);
  endproperty
 
  property eof_last;
    @(posedge clk) disable iff (rst) 
    (($past(strm.eof) && $past(strm.val)) |-> !strm.val);
  endproperty
 
  property bad_length;
    @(posedge clk) disable iff (rst) 
    (strm.sof |-> ##48 !strm.val);
  endproperty
 
  ERROR_SOF_LENGTH: assert property (sof_one_tick) else $error("SOF was high more then 1 tick");
  ERROR_SOF_VAL:    assert property (sof_with_val) else $error("SOF was high when VAL was low");
  ERROR_SOF_FIRST:  assert property (sof_first)    else $error("SOF did not appear for 1st byte");
 
  ERROR_EOF_LENGTH: assert property (eof_one_tick) else $error("EOF was high more then 1 tick");
  ERROR_EOF_VAL:    assert property (eof_with_val) else $error("EOF was high when VAL was low");
  ERROR_EOF_LAST:   assert property (eof_last)     else $error("EOF did not appear for last byte");
  
endmodule : mac_vlg_rx_sva
