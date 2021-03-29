interface udp;
  import ipv4_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import udp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  stream_t   strm;
  logic      rdy;  // Data ready from to IPv4
  logic      req;  // Data request for tx when done with header
  logic      done;
  logic      ack;
  udp_meta_t meta;
   
  modport in_rx  (input  strm, meta);
  modport out_rx (output strm, meta);
  modport in_tx  (input  strm, meta, rdy, output req, ack, done);
  modport out_tx (output strm, meta, rdy, input  req, ack, done);
  modport sva    (input  strm, meta, rdy,        req, ack, done);
endinterface : udp
