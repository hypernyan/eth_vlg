interface tcp_ifc; // used to connect rx and tx modules to logic
  import tcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  stream_t    strm; // stream of tcp data (with header)
  tcp_meta_t  meta; // tcp metadata
  logic       rdy;  // data ready to IPv4
  logic       req;  // data tcp pacet request for when done transmitting header
  logic       acc;  // data accepted, logic may continue operation
  logic       done; // transmisssion finished

  modport in_rx  (input  strm, meta); // received path has no flow control,
  modport out_rx (output strm, meta); // exclude unncessary ports
  modport in_tx  (input  strm, meta, rdy, output req, acc, done);
  modport out_tx (output strm, meta, rdy, input  req, acc, done);
  modport sva    (input  strm, meta, rdy,        req, acc, done);
endinterface : tcp_ifc