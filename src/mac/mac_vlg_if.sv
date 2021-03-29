interface mac;
import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

  logic      rdy;
  logic      req;
  logic      acc;
  logic      done;
  
  stream_t   strm;
  mac_meta_t meta;  // MAC header
  
  modport in_rx  (input  strm, meta);
  modport out_rx (output strm, meta);
  
  modport in_tx  (input  rdy, strm, meta, output req, acc, done);
  modport out_tx (output rdy, strm, meta, input  req, acc, done);

  modport sva    (input  rdy, strm, meta,        req, acc, done);
endinterface : mac
