interface tcp_rx_ctl_ifc; // connects rx_ctl module to engine and receive part of ui
  import tcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  tcp_stat_t     status;   // engine status
  logic          flush;    // engine request to flush buffer
  logic          flushed;  // rx_ctl response that RAM flush is complete
  tcb_t          tcb;      // engine's current transmission control block
  stream_t       strm;     // path for received raw tcp data stream
  logic          init;     // engine's sigal to initialize local ack from tcb
  tcp_num_t      loc_ack;  // current value reported by rx_ctl
  logic          send_ack; // rx_ctl's signal to send ack
  logic          ack_sent; // rx_ctl response that ack was sent
  tcp_opt_sack_t loc_sack; // local SACK blocks reported by rx_ctl
  modport in  (input  status, flush, tcb, strm, init, ack_sent, output flushed, loc_ack, loc_sack, send_ack); 
  modport out (output status, flush, tcb, strm, init, ack_sent, input  flushed, loc_ack, loc_sack, send_ack);
  modport sva (input  status, flush, tcb, strm, init, ack_sent,        flushed, loc_ack, loc_sack, send_ack);
endinterface : tcp_rx_ctl_ifc
