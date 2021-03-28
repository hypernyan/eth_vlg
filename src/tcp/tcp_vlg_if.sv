interface tcp; // used to connect rx and tx modules to logic
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
endinterface : tcp

interface tcp_ctl; // provide control over tcp connection
  import ipv4_vlg_pkg::*;
  import tcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  logic       connect;  // try to establish a connection
  logic       listen;   // transiton to listen state
  ipv4_t      rem_ipv4; // set target remote ip
  port_t      rem_port; // set target remote port
  port_t      loc_port; // set local port
  tcp_stat_t  status;   // tcp engine status

  modport in  (input  connect, listen, rem_ipv4, rem_port, loc_port, output status);
  modport out (output connect, listen, rem_ipv4, rem_port, loc_port, input  status);
endinterface : tcp_ctl

interface tcp_data;
  logic [7:0] dat; // data input
  logic       val; // data valid input
  logic       err; // error for rceive path only
  logic       cts; // transmission clear to send. user has 1 tick to deassert vin before data is lost
  logic       snd; // force sending all buffd data not waiting for TCP_WAIT_TICKS

  modport in_rx  (input  dat, val, err);
  modport out_rx (output dat, val, err);
  modport in_tx  (input  dat, val, snd, output cts);
  modport out_tx (output dat, val, snd, input  cts);
endinterface : tcp_data

interface rx_ctl; // connects rx_ctl module to engine and receive part of ui
  import tcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  tcp_stat_t status;   // engine status
  logic      flush;    // engine request to flush buffer
  logic      flushed;  // rx_ctl response that RAM flush is complete
  tcb_t      tcb;      // engine's current transmission control block
  stream_t   strm;     // user's receive path for raw tcp data stream
  logic      init;     // engine's sigal to initialize local ack from tcb
  tcp_num_t  loc_ack;  // current value reported by rx_ctl
  logic      send_ack; // rx_ctl's signal to send ack
  logic      ack_sent; // rx_ctl response that ack was sent

  modport in  (input  status, flush, tcb, strm, init, ack_sent, output flushed, loc_ack, send_ack); 
  modport out (output status, flush, tcb, strm, init, ack_sent, input  flushed, loc_ack, send_ack);
  modport sva (input  status, flush, tcb, strm, init, ack_sent,        flushed, loc_ack, send_ack);

endinterface : rx_ctl

interface tx_ctl; // connects tx_ctl module to engine and transmit part of ui
  import tcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  tcp_stat_t     status;    // engine status
  logic          flush;     // engine request to flush buffer
  logic          flushed;   // tx_ctl response that RAM flush is complete
  tcb_t          tcb;       // engine's current transmission control block
  stream_t       strm;      // user's transmit path for raw tcp data stream
  logic          init;      // engine's sigal to initialize local seq from tcb
  tcp_num_t      loc_seq;   // current value reported by tx_ctl
  // sending forced acks with loc_seq higher then last reported 
  // i.e. when a packet's not yet formed, but loc_seq is already higher
  // may result in out of order situation. 
  // so, report last seq sent with payload for 0 payload packets
  tcp_num_t      last_seq;  // last actually transmitted seq num
  logic          rst;       // engine's request to reset transmission control
  tcp_pld_info_t pld_info;  // current payload info to form a tcp packet. goes to tx_arb
  logic          send;      // tx_ctl indicates a packet is ready for transmission
  logic          req;       // engine requests tcp stream
  logic          sent;      // engine reports that packet was sent
  logic          force_dcn; // tx_ctl requests connection abort if retransmissions failed to increase remote seq
  modport in  (input  status, flush, tcb, req, sent, init, rst, output flushed, send, pld_info, strm, loc_seq, last_seq, force_dcn);
  modport out (output status, flush, tcb, req, sent, init, rst,  input flushed, send, pld_info, strm, loc_seq, last_seq, force_dcn);
endinterface : tx_ctl
