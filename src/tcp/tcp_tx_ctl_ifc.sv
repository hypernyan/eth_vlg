interface tcp_tx_ctl_ifc; // connects tx_ctl module to engine and transmit part of ui
  import tcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  tcp_stat_t     status;      // engine status
  logic          flush;       // engine request to flush buffer
  logic          flushed;     // tx_ctl response that RAM flush is complete
  tcb_t          tcb;         // engine's current transmission control block
  stream_t       strm;        // user's transmit path for raw tcp data stream
  logic          init;        // engine's sigal to initialize local seq from tcb
  tcp_num_t      loc_seq;     // current value reported by tx_ctl
  // since sequence number in TCB is incremented at writing each byte
  // sending pure acks with seq higher then last reported 
  // i.e. when a packet's not yet formed, but pure ack is sent with new seq
  // may result in out of order situation. 
  // to avoid that, always report sequence of the last actually sent byte 
  tcp_num_t      last_seq;    // last actually transmitted seq
  tcp_num_t      dup_ack;    // duplicate ack number received
  logic          dup_det;    // dup_ack is valid, dup acks were received
  logic          rst;         // engine's request to reset transmission control
  tcp_pld_info_t pld_info;    // current payload info to form a tcp packet. goes to tx_arb
  logic          send;        // tx_ctl indicates a packet is ready for transmission
  logic          req;         // engine requests tcp stream
  logic          sent;        // engine reports that packet was sent
  logic          force_dcn;   // tx_ctl requests connection abort if retransmissions failed to increase remote seq
  modport in  (input  status, flush, tcb, dup_ack, dup_det, req, sent, init, rst, output flushed, send, pld_info, strm, loc_seq, last_seq, force_dcn);
  modport out (output status, flush, tcb, dup_ack, dup_det, req, sent, init, rst,  input flushed, send, pld_info, strm, loc_seq, last_seq, force_dcn);
  modport sva (input  status, flush, tcb, dup_ack, dup_det, req, sent, init, rst,        flushed, send, pld_info, strm, loc_seq, last_seq, force_dcn);
endinterface : tcp_tx_ctl_ifc
