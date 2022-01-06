interface ipv4_ifc ();
  import ipv4_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import tcp_vlg_pkg::*;

  stream_t    strm;
  logic       rdy;
  logic       req;
  logic       acc;
  logic       err;
  logic       done;
  ipv4_meta_t meta;

  modport in_tx  (input  strm, meta, rdy, output req, acc, err, done); // used for transmitting ipv4 
  modport out_tx (output strm, meta, rdy, input  req, acc, err, done); // used for transmitting ipv4 
  modport sva    (input strm, meta, rdy,         req, acc, err, done); // used for transmitting ipv4 

  modport in_rx  (input  strm, meta); // used for receiving ipv4 
  modport out_rx (output strm, meta); // used for receiving ipv4 
endinterface : ipv4_ifc
