import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

interface mac;
  logic      rdy;
  logic      req;
  logic      ack;
  logic      done;
  
  stream_t   strm;
  mac_meta_t meta;  // MAC header
  
  modport in_rx  (input  strm, meta);
  modport out_rx (output strm, meta);
  
  modport in_tx  (input  rdy, strm, meta, output req, ack, done);
  modport out_tx (output rdy, strm, meta, input  req, ack, done);
endinterface : mac
