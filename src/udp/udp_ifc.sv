interface udp_ifc;
  import udp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  stream_t   strm;
  logic      rdy;  // Data ready to IPv4
  logic      req;  // Data request for tx when done with header
  logic      acc;
  logic      err;
  logic      done;
  udp_meta_t meta;
   
  modport in_rx  (input  strm, meta);
  modport out_rx (output strm, meta);
  modport in_tx  (input  strm, meta, rdy, output acc, err, req, done);
  modport out_tx (output strm, meta, rdy, input  acc, err, req, done);
  modport sva    (input  strm, meta, rdy,        acc, err, req, done);
endinterface : udp_ifc
