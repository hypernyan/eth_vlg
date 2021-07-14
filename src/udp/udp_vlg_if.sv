interface udp;
  import ipv4_vlg_pkg::*;
  import udp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  stream_t   strm;
  logic      rdy;  // Data ready to IPv4
  logic      req;  // Data request for tx when done with header
  logic      done;
  udp_meta_t meta;
   
  modport in_rx  (input  strm, meta);
  modport out_rx (output strm, meta);
  modport in_tx  (input  strm, meta, rdy, output req, done);
  modport out_tx (output strm, meta, rdy, input  req, done);
  modport sva    (input  strm, meta, rdy,        req, done);
endinterface : udp

interface udp_data;
  logic [7:0] dat; // data input
  logic       val; // data valid input
  logic       err; // error for rceive path only
  logic       cts; // transmission clear to send. User should countinue sending current datagram even if '0'

  modport in_rx  (input  dat, val, err);
  modport out_rx (output dat, val, err);
  modport in_tx  (input  dat, val, output cts);
  modport out_tx (output dat, val, input  cts);
  modport sva    (input  dat, val,        cts);
endinterface : udp_data

interface udp_ctl; // provide control over udp connection
  port_t      loc_port; // local port

  ipv4_t      ipv4_rx;     // current datagram source ip
  port_t      rem_port_rx; // target remote port
  
  length_t    length;      // current frame length
  ipv4_t      ipv4_tx;     // target ip for transmission
  port_t      rem_port_tx; // target remote port

  modport in  (input  ipv4_tx, rem_port_tx, loc_port, length, output ipv4_rx, rem_port_rx);
  modport out (output ipv4_tx, rem_port_tx, loc_port, length, input  ipv4_rx, rem_port_rx);
  modport sva (input  ipv4_tx, rem_port_tx, loc_port, length,        ipv4_rx, rem_port_rx);
endinterface : udp_ctl