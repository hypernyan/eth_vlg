/* manage data queuing, retransmissions and chsum calculation
   incoming data is stored in RAM of size 2^RAM_DEPTH
   if user doesn't send data for WAIT_TICKS or MAX_PAYLOAD_LEN is reached with no interruptions in in_v, 
   packed is queued and an entry in fifo_queue_ram is added. 
   Each entry contains info necessary for server and tx module to send user data:
     - present flag which indicates that the packet is unacked and is still queued
     - chsum for this payload
     - seq - start address for the packet in raw data buffer
     - length of the packet ecpressed in bytes
     - timer - timer to retransmit unacked packets
     - tries - times server has tried to retransmit the packet

.                     ________                      _____
.                    |raw data|===read packet=====>|     |
.                    |  RAM   |                    |     |
.                    |        |                    |TCP  |
.                    | port B |                    | tx  |                 
.                    |        | tx                 |     |                 
.                    | port A |======>             |_____|  
.                    |________|                                 
.                     _________    ________   tx         
.                    | port A  |=>|  scan  |=======> 
.                    |__(add)__|<=|  FSM   |pending 
.                    | packet  |  |________|  
.         ______     |  info   |
.        |      |    |  RAM    |
.        | new  |    |_________|     
.        |packet|===>| port B  |  
.        |adder |    |_(clear)_|
         |______|               
                       








*/
import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_tx_queue #(
  parameter integer MAX_PAYLOAD_LEN  = 1400, // Maximum payload length
  parameter integer RETRANSMIT_TICKS = 1000000,
  parameter integer RETRANSMIT_TRIES = 5,
  parameter integer RAM_DEPTH        = 10,
  parameter integer PACKET_DEPTH     = 3,
  parameter integer WAIT_TICKS       = 20
)
(
  input   logic             clk,
  input   logic             rst,
  input   dev_t             dev,
  input   logic [7:0]       in_d,
  input   logic             in_v,
  output  logic             cts,
  input   logic             tx_busy,
  input   logic             tx_done,
  input   logic [31:0]      rem_ack,
  output  logic [31:0]      seq,  // packet's seq
  input   logic [31:0]      isn,  // packet's seq
  output  logic [7:0]       data, //in. data addr queue_addr 
  input   logic [RAM_DEPTH-1:0] addr, //out.
  output  logic             pending,  //in. packet ready in queue
  output  logic [15:0]      len,  // packet's len
  output  logic [31:0]      payload_chsum,

  output logic force_fin,
  input  logic connected,
  input  logic flush_queue,  
  output logic queue_flushed
);

tcp_pkt_t upd_pkt, upd_pkt_q, new_pkt, new_pkt_q;

logic [PACKET_DEPTH
-1:0] new_addr, upd_addr, upd_addr_prev;
logic [$clog2(MAX_PAYLOAD_LEN+1)-1:0] ctr;
logic [$clog2(WAIT_TICKS+1)-1:0] timeout;
logic [31:0] chsum;
logic [31:0] cur_seq, ack_diff;
logic [RAM_DEPTH-1:0] space_left;
logic [7:0] in_d_prev;
logic in_v_prev;
logic connected_prev, load_pend;

logic fifo_rst, fsm_rst, upd_cts, load, upd, chsum_rst;

logic free, retrans;
logic [$clog2(RETRANSMIT_TICKS+1)+RETRANSMIT_TRIES:0] timer;
logic [1:0] tries;

tcp_data_queue #(
  .D (RAM_DEPTH),
  .W (8)
) tcp_data_queue_inst (
  .rst (fifo_rst),
  .clk (clk),
 
  .w_v (in_v),
  .w_d (in_d),
  .seq (cur_seq),
  .isn (isn),
  .space_left (space_left),
  .rd_addr (addr),
  .ack (ack),
  .r_q (data),

  .f (full),
  .e (empty)
);

// raw tcp data is kept here
fifo_queue_ram #(PACKET_DEPTH
) fifo_queue_ram_inst (.*);

logic [PACKET_DEPTH
:0] new_ptr, new_ptr_ahead, free_ptr, diff, flush_ctr;

assign diff = new_ptr_ahead - free_ptr;
assign cts = connected && !diff[PACKET_DEPTH
] && !full;

assign new_addr[PACKET_DEPTH
-1:0] = new_ptr[PACKET_DEPTH
-1:0];

enum logic {
  w_idle_s,
  w_pend_s
} w_fsm;

logic load_timeout, load_mtu, load_full;

always @ (posedge clk) begin
  connected_prev <= connected;
  fifo_rst <= rst || (connected_prev != connected);
end

assign load_timeout = (timeout == WAIT_TICKS && !in_v);
assign load_mtu     = (ctr == MAX_PAYLOAD_LEN);
assign load_full    = full;

assign load_pend = (w_fsm == w_pend_s) && (load_timeout || load_mtu || load_full);   
assign new_pkt.length = ctr; // length equals byte count for current packet. together with seq logic reads out facket from fifo
assign new_pkt.chsum = ctr[0] ? chsum + {in_d_prev, 8'h00} : chsum;
assign new_pkt.present = 1; // this packet is pendingid in memory
assign new_pkt.tries = 0;
assign new_pkt.timer = RETRANSMIT_TICKS; // preload so packet is read out asap the first time

always @ (posedge clk) begin
  if (fifo_rst || flush_queue) begin
    ctr     <= 0;
    new_ptr <= 0;
    load    <= 0;
    timeout <= 0;
    cur_seq <= isn;
    w_fsm <= w_idle_s;
  end
  else begin
    new_pkt.stop  <= cur_seq; // equals expected ack for packet
    new_pkt.start <= cur_seq - ctr; // equals packet's seq
    if (in_v) begin
      in_d_prev <= in_d;
      cur_seq <= cur_seq + 1;
    end
    case (w_fsm)
      w_idle_s : begin
        if (in_v) w_fsm <= w_pend_s;
        ctr <= 1; // Can't add packet with zero length
        load <= 0;
        chsum <= 0;
        timeout <= 0;
      end
      w_pend_s : begin // Pending load
        if (in_v) begin
          ctr <= ctr + 1;
          chsum <= (ctr[0]) ? chsum + {in_d_prev, in_d} : chsum;
        end
        timeout <= (in_v) ? 0 : timeout + 1; // reset timeout if new byte arrives
        // either of three conditions to load new pakcet
        if (load_full || load_timeout || load_mtu) w_fsm <= w_idle_s;
      end
    endcase
    load <= load_pend; // load packet 1 tick after 'pending'
//    if (load) $display("%d.%d.%d.%d:%d: Queuing packet: seq:%h,nxt seq:%h, len:%d. space: %d", dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], dev.tcp_port, cur_seq - ctr, cur_seq, ctr, space_left);
    if (load) new_ptr <= new_ptr + 1;
    new_ptr_ahead <= new_ptr + 1;
  end
end

enum logic [6:0] {
  queue_scan_s,
  queue_check_s,
  queue_read_s,
  queue_next_s,
  queue_wait_s,
  queue_retrans_s,
  queue_flush_s
} fsm;

// remote host may acknowledge some part of the packet (mainly when sending data of length > remote host window)
// queue RAM frees space based on ack_num
// have to check if received ack_num acknowledges whole packet, otherwise data may be overwritten and checksum will be incorrect
// pass packet's expected ack instead of remote ack

// - free space          p s      r a          p a          
// = valid data          k e      e c          k c          
// x overwritten data    t q      m k          t k         
// -----------------------|========|============|-------- 
// -----------------------|========|xxxxxxxxxxxx|-------- data loss if remote ack is passed directly to queue RAM

logic [31:0] ack, stop;

always @ (posedge clk) begin
  if (fifo_rst || rst) begin
    fsm           <= queue_scan_s;
    upd           <= 0;
    upd_addr      <= 0;
    force_fin     <= 0;
    pending       <= 0;
    free_ptr      <= 0;
    flush_ctr     <= 0;
    fsm_rst       <= 0;
    queue_flushed <= 0;
    upd_pkt       <= 0;
	  ack           <= rem_ack;
    tries <= 0;
    timer <= 0;
    free <= 0;
  end
  else begin
	  payload_chsum <= upd_pkt_q.chsum;
	 // seq           <= upd_pkt_q.start;
	 // len           <= upd_pkt_q.length;
    // don't change these fields:
    upd_pkt.chsum  <= upd_pkt_q.chsum;
    upd_pkt.start  <= upd_pkt_q.start;
    upd_pkt.stop   <= upd_pkt_q.stop;
    upd_pkt.length <= upd_pkt_q.length;
    upd_addr_prev  <= upd_addr;
    case (fsm)
      queue_scan_s : begin
        upd <= 0;
        queue_flushed <= 0;
        // Continiously scan for unacked packets. If present flag found, check if it's acked (queue_check_s)
         // if packet at current address is not present, read next
        if (flush_queue) fsm <= queue_flush_s;
        else if (upd_pkt_q.present) begin // if a packet is present (not yet acknowledged and stored in RAM)
          fsm <= queue_read_s; // read its pointers and length
          upd_addr <= upd_addr_prev;
          ack_diff <= upd_pkt_q.stop - rem_ack; // ack_diff[31] means either ack or exp ack ovfl
          timer <= upd_pkt_q.timer;
          tries <= upd_pkt_q.tries;
          stop <= upd_pkt_q.stop;
          free <= 0;
          retrans <= 0;
          seq <= upd_pkt_q.start;
	        len <= upd_pkt_q.length;
        end
        else upd_addr <= upd_addr + 1;
      end
      queue_read_s : begin
        fsm <= queue_check_s;
        if (ack_diff[31] || ack_diff == 0) begin // || ack_diff == 0) begin
			    free <= 1;
		    end
		    else if (!ack_diff[31] && (timer == RETRANSMIT_TICKS)) retrans <= 1;
      end
      queue_check_s : begin
        if (!tx_busy && !load && !load_pend) begin
          upd <= 1;
          if (free) begin // clear present flag if acked
          //  free_ptr <= free_ptr + 1;
            fsm <= queue_next_s;
            upd_pkt.present <= 0;
            upd_pkt.timer <= 0;
            upd_pkt.tries <= 0;
            pending <= 0;
          end
          else if (retrans) begin 
            fsm <= queue_retrans_s;
            if (tries == RETRANSMIT_TRIES) force_fin <= 1;
            upd_pkt.present <= 1;
            upd_pkt.timer <= 0;
            upd_pkt.tries <= tries + 1;
            pending <= 1;
          end
          else begin
            fsm <= queue_next_s;
            upd_pkt.present <= 1;
            upd_pkt.timer <= timer + 1;
            upd_pkt.tries <= tries; // increment retransmit timer
            pending <= 0;
          end
        end
      end
      queue_next_s : begin
        if (free) begin
          free_ptr <= free_ptr + 1;
          ack <= stop;
        end
        upd <= 0;
        upd_addr_prev <= upd_addr + 1;
        upd_addr <= upd_addr + 1;
        fsm <= queue_wait_s;
      end
      queue_wait_s : begin
        fsm <= queue_scan_s;
      end
      queue_retrans_s : begin
        upd <= 0;
        if (tx_done) begin
          fsm <= queue_scan_s;
          pending <= 0;
          upd_addr <= upd_addr + 1;
        end
      end
      queue_flush_s : begin
        pending <= 0;
        upd_addr <= upd_addr + 1;
        upd_pkt.present <= 0;
        upd <= 1;
        flush_ctr <= flush_ctr + 1;
        if (flush_ctr == 0 && upd) begin
          queue_flushed <= 1;
        //  fsm_rst <= 1;
        end
      end
      default : begin
        force_fin <= 1;
        upd <= 0;
        pending <= 0;
        fsm <= queue_scan_s;
        upd_pkt.present <= 0;
        upd_pkt.timer <= 0;
        upd_pkt.tries <= 0;
      end
    endcase
  end
end

endmodule : tcp_vlg_tx_queue

module fifo_queue_ram #(
  parameter PACKET_DEPTH
 = 8
)
(
  input  logic     clk,
  input  logic     load,
  input  logic     upd,
  input  tcp_pkt_t new_pkt,
  output tcp_pkt_t new_pkt_q,
  input  tcp_pkt_t upd_pkt,
  output tcp_pkt_t upd_pkt_q,
  input  logic [PACKET_DEPTH
-1:0] new_addr,
  input  logic [PACKET_DEPTH
-1:0] upd_addr
);

tcp_pkt_t pkt_info [0:2**(PACKET_DEPTH
)-1];
// initial pkt_info = 0;

initial for (int i = 0; i < 2**PACKET_DEPTH
; i = i + 1) pkt_info[i] = '0;

always @ (posedge clk) begin
  if (load) begin
    pkt_info[new_addr] <= new_pkt;
    new_pkt_q <= new_pkt;
  end
  else new_pkt_q <= pkt_info[new_addr];
end

always @ (posedge clk) begin
  if (upd) begin
    pkt_info[upd_addr] <= upd_pkt;
    upd_pkt_q <= upd_pkt;
  end
  else upd_pkt_q <= pkt_info[upd_addr];
end

endmodule : fifo_queue_ram

// Hold raw TCP data to be transmitted, free space when ack received
module tcp_data_queue #(
  parameter D = 16,
  parameter W = 16
)
(
  input  logic         rst,
  input  logic         clk,
  
  input  logic         w_v,
  input  logic [W-1:0] w_d,
  input  logic [31:0]  seq,
  input  logic [31:0]  isn,
  input  logic [31:0]  ack, // free bytes when ack received
  output logic [D-1:0] space_left,
  input  logic [D-1:0] rd_addr, // address to read from 
  output logic [W-1:0] r_q,
  
  output logic         f,
  output logic         e
);

logic [D-1:0] wr_addr;
logic [32:0]  diff;

assign diff = seq - ack;
assign space_left = (diff[D]) ? 0 : ~diff[D-1:0];

assign e = (diff == 0);
assign f = (space_left == 0);

always @ (posedge clk) begin
  if (rst) wr_addr[D-1:0] <= isn[D-1:0];
  else if (w_v) wr_addr <= wr_addr + 1;
end

reg [W-1:0] mem[(1<<D)-1:0];

always @ (posedge clk) r_q <= mem[rd_addr];

always @ (posedge clk) if (w_v) mem[wr_addr] <= w_d;

endmodule : tcp_data_queue
