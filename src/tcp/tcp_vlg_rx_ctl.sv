module tcp_vlg_rx_ctl
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
 #(
  parameter int    ACK_TIMEOUT       = 20,
  parameter int    FORCE_ACK_PACKETS = 5,
  parameter int    RAM_DEPTH         = 15,
  parameter bit    VERBOSE           = 0,
  parameter string DUT_STRING        = ""
)
(
  input    logic  clk,
  input    logic  rst,
  input    dev_t  dev,
  tcp.in_rx       rx,  // incomming tcp and metadata
  rx_ctl.in       ctl, // rx control interface with engine
  tcp_data.out_rx data // user inteface (received raw TCP stream output)
);

  // 2. generates pure Acks (w/o payload) if either:
  //   - timeout has passed
  //   - unacked packet count exceeded threshold 
  //   - sack was updated
  // 3. reports length of packets to be read from rx queue 
  // these Acks are the TCP informative logic
  // they do not carry data nor increase sequence number
  tcp_vlg_ack #(
    .TIMEOUT           (ACK_TIMEOUT),
    .FORCE_ACK_PACKETS (FORCE_ACK_PACKETS), // Force ack w/o timeout if this amount of packets was received
    .VERBOSE           (VERBOSE),
    .DUT_STRING        (DUT_STRING)
  ) tcp_vlg_ack_inst (
    .clk      (clk),
    .rst      (rst),
    .rx       (rx),
    .tcb      (ctl.tcb),
    .init     (ctl.init),
    .loc_ack  (ctl.loc_ack),
    .status   (ctl.status),
    .send     (ctl.send_ack),    // send pure ack upon ack timeout, exceeding unacked received packets count or 
    .sent     (ctl.ack_sent),    // tx logic will confirm as soon as packet is sent
    .sack_upd (sack_upd)
  );

  // manages SACK option
  // holds rx queue (SACK blocks)


  // 1. manages Ack number
  // 2. manages writing SACK blocks and their reassembly
  // 3. interfaces rx part of user logic
  tcp_vlg_sack #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING),
    .RAM_DEPTH  (RAM_DEPTH)
  ) tcp_vlg_sack_inst (
    .clk     (clk),
    .rst     (rst),
    .rx      (rx),
    .tcb     (ctl.tcb),
    .data    (data),         // ordered user data to output
    .init    (ctl.init),
    .loc_ack (ctl.loc_ack),  // current local ack number
    .status  (ctl.status),   // connection status
    .sack    (ctl.loc_sack), // current SACK option to be reported
    .upd     (sack_upd)      // send pure Ack upon any SACK block change
  );

endmodule : tcp_vlg_rx_ctl
