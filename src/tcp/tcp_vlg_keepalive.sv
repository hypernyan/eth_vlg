import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_keepalive #(
  parameter int PERIOD   = 600000000,
  parameter int INTERVAL = 125000000,
  parameter bit ENABLE   = 1,
  parameter int TRIES    = 5,
  parameter bit VERBOSE  = 0
)
(
  input  logic clk,
  input  logic rst,
  input  tcb_t tcb,
  tcp.in_rx    rx,  
  output logic send, // Send send event
  input  logic sent,
  output logic dcn,  // Force disconnect
  input  tcp_stat_t status   // TCP is connected
);

  logic [$clog2(PERIOD+1)-1:0] timer;
  logic [$clog2(TRIES+1)-1:0]  tries;
  
  logic con_flt;
  logic seq_ack_equal;
  assign port_match = rx.meta.tcp_hdr.dst_port == tcb.loc_port && rx.meta.tcp_hdr.src_port == tcb.rem_port;
  assign con_flt = rx.meta.val && port_match;
  assign seq_ack_equal = con_flt && (rx.meta.tcp_hdr.tcp_seq_num == tcb.loc_ack);
  logic int_rst;
  
  always @ (posedge clk) if (rst) int_rst <= 1; else int_rst <= (status != tcp_connected);

  always @ (posedge clk) begin
    if (int_rst) begin
      timer   <= 0; 
      tries   <= 0; 
      send    <= 0;
      dcn     <= 0;
    end
    else begin
      if (con_flt) begin // 
        timer <= 0; // if packet arrives, restart ack timeout counter 
        tries <= 0; // reset keep-alive tries (connection is definitely active)
      end
      else begin
        timer <= (timer == PERIOD - 1) ? 0         : timer + 1;
        tries <= (timer == TRIES  - 1) ? tries + 1 : tries;
      end
      if (timer == PERIOD - 1) send <= 1; else if (sent) send <= 0;
      // If there were TRIES to send ka but 
      // no packets were received from remote host,
      // request tcp engine to disconnect
      if (tries == TRIES - 1) dcn <= 1; 
    end
  end

endmodule : tcp_vlg_keepalive
