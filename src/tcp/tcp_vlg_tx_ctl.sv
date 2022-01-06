module tcp_vlg_tx_ctl 
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int    MTU                   = 1500,
  parameter int    RETRANSMIT_TICKS      = 1000000,
  parameter int    FAST_RETRANSMIT_TICKS = 10000,
  parameter int    SACK_RETRANSMIT_TICKS = 10000,
  parameter int    RETRANSMIT_TRIES      = 5,
  parameter int    RAM_DEPTH             = 10,
  parameter int    PACKET_DEPTH          = 3,
  parameter int    WAIT_TICKS            = 20,
  parameter bit    VERBOSE               = 0,
  parameter string DUT_STRING            = ""
)
(
  input logic        clk,
  input logic        rst,
  input dev_t        dev,
  tcp_data_ifc.in_tx data, // user inteface (raw TCP stream)
  tcp_tx_ctl_ifc.in  ctl   // engine is connected via this ifc
);

  logic info_full;
  logic empty, full;
  logic upd;
  logic buf_rst;
  logic add_pend;
  logic free;
  
  logic tx_idle;
  logic add;
  logic tx_pend;
  tcp_pkt_t new_pkt, upd_pkt_w, upd_pkt_r;
  logic [PACKET_DEPTH-1:0] add_ptr, upd_ptr;
  logic [RAM_DEPTH-1:0] buf_addr;
  tcp_num_t last_ack;

  tcp_vlg_seq tcp_vlg_seq_inst (
    .clk  (clk),
    .tcb  (ctl.tcb),
    .val  (data.val),
    .init (ctl.init),
    .seq  (ctl.loc_seq)
  );
  
  assign data.cts = (ctl.status == tcp_connected) && !info_full && !full;

  tcp_vlg_tx_add #(
    .WAIT_TICKS (WAIT_TICKS),
    .MTU        (MTU)
  ) tcp_vlg_tx_add_inst (
    .clk   (clk),
    .rst   (ctl.rst),
    .seq   (ctl.loc_seq),
    .pkt   (new_pkt),
    .add   (add),
    .pend  (add_pend),
    .full  (full),
    .flush (ctl.flush),
    .val   (data.val),
    .dat   (data.dat),
    .snd   (data.snd)
  );

  tcp_vlg_tx_info #(
    .D (PACKET_DEPTH)
  ) tcp_vlg_tx_info_inst (
    .clk (clk),
    .rst (ctl.rst || ctl.init),
    // new packets (tx_add)
    .new_pkt (new_pkt),
    .add     (add),
    .free    (free),
    // update packets (tx_scan)
    .ptr   (upd_ptr),
    .pkt_w (upd_pkt_w),
    .pkt_r (upd_pkt_r),
    .upd   (upd),
    .full  (info_full)
  );

  tcp_vlg_tx_scan #(
    .MTU                   (MTU),                  
    .RETRANSMIT_TICKS      (RETRANSMIT_TICKS),     
    .SACK_RETRANSMIT_TICKS (SACK_RETRANSMIT_TICKS),
    .RETRANSMIT_TRIES      (RETRANSMIT_TRIES),     
    .PACKET_DEPTH          (PACKET_DEPTH),         
    .VERBOSE               (VERBOSE),              
    .DUT_STRING            (DUT_STRING)
  ) tcp_vlg_tx_scan_inst (  
    .clk (clk),
    .rst (ctl.rst || ctl.init),
    
    .dev       (dev),
    .tcb       (ctl.tcb),
    .add_pend  (add_pend),
    .upd       (upd),
    .free      (free),
    .ptr       (upd_ptr),
    .pkt_r     (upd_pkt_r),
    .pkt_w     (upd_pkt_w),
    .last_ack  (last_ack),  
    .pld_info  (ctl.pld_info), 
    .pend      (tx_pend),
    .force_dcn (ctl.force_dcn),
    .flush     (ctl.flush),    
    .flushed   (ctl.flushed),  
    .dup_det   (ctl.dup_det),  
    .dup_ack   (ctl.dup_ack),
    .tx_idle   (tx_idle)
  );

  tcp_vlg_tx_strm  #(
    .D (RAM_DEPTH)
  ) tcp_vlg_tx_strm_inst (
    .clk      (clk),
    .rst      (ctl.rst || ctl.init),
    .pend     (tx_pend),
    .send     (ctl.send),
    .sent     (ctl.sent),
    .req      (ctl.req),
    .last_seq (ctl.last_seq),
    .pld_info (ctl.pld_info),
    .tcb      (ctl.tcb),
    .addr     (buf_addr),
    .val      (ctl.strm.val),
    .sof      (ctl.strm.sof),
    .eof      (ctl.strm.eof),
    .idle     (tx_idle)
  );

  always_ff @ (posedge clk) buf_rst <= ctl.init;

  tcp_vlg_tx_buf #(
    .D (RAM_DEPTH),
    .W (8)
  ) tcp_vlg_tx_buf_inst (
    .rst (buf_rst),
    .clk (clk),

    .data_in  (data.dat),    // user data
    .write    (data.val),    // user data valid
    .seq      (ctl.loc_seq), // local seqence number
    
    .ack      (last_ack),      // highest recorded remote ack number 
    .addr     (buf_addr),     // address to read from
    .data_out (ctl.strm.dat), // data at 'addr' (1 tick delay)

    .f (full),
    .e (empty)
  );

endmodule
