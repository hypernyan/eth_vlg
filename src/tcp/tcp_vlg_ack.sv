import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

// Acknowledgement control:
// Keeps track of local acknowledgement number
// loc ack is always valid after init goes low
// loc_ack in TCB is updated upon sending a packet with that ack

module tcp_vlg_ack #(
  parameter int TIMEOUT = 1250
)
(
  input  logic      clk,
  input  logic      rst,
  tcp.in_rx         rx,
  input  tcp_stat_t status,

  input  tcb_t      tcb,  // contains initial loc_ack or 
  input  logic      init, // init_loc_ack is valid
 
  output tcp_num_t  loc_ack, // local acknowledgement number
 
  output logic      send, // send pure ack upon ack timeout
  input  logic      sent
);

  logic [31:0] diff;

  logic [$clog2(TIMEOUT+1)-1:0] timer;
  logic acked; // data is acked, no need to do anything

  tcp_num_t rem_seq;

  assign diff = rem_seq - loc_ack;

  // Derive ack from rem seq. Ignore 
  always @ (posedge clk) begin
    if (rst) begin
      loc_ack <= 0;
      acked   <= 0;
      rem_seq <= 0;
    end
    else begin
      if (init) loc_ack <= tcb.loc_ack;
      else if (rx.meta.val) begin
        // update remote sequence from incoming packets.
        rem_seq <= rx.meta.tcp_hdr.tcp_seq_num + rx.meta.pld_len;
        //
        if ((diff[31] && (rem_seq < loc_ack)) || (!diff[31] && (rem_seq > loc_ack))) loc_ack <= rem_seq;
      end
      else if (status == tcp_connected) begin // todo: rm else?
        acked <= (loc_ack == tcb.loc_ack);
      end
    end
  end
 
  ///////////////
  // Ack timer //
  ///////////////

  always @ (posedge clk) begin
    if (rst) begin
      timer <= 0;
      send  <= 0;
    end
    else begin
      if (status == tcp_connected) begin
        // keep timer reset if acked
        // or reset timer after receiving unacked packet
        if (acked || (rx.meta.val && (rx.meta.tcp_hdr.tcp_seq_num + rx.meta.pld_len) != loc_ack)) timer <= 0;
        // keep timer at TIMEOUT until 
        else timer <= (timer == TIMEOUT) ? TIMEOUT : timer + 1;
        // Reset send flag after packet was sent, but don't hold it to '1'
        if (timer == TIMEOUT - 1) send <= 1; else if (sent) send <= 0;
      end 
      else send <= 0;
    end
  end 

endmodule : tcp_vlg_ack