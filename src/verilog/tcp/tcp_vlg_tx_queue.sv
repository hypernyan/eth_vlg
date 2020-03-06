/* manage data queuing, retransmissions and checksum calculation
   incoming data is stored in RAM of size 2^RAM_DEPTH
   if user doesn't send data for WAIT_TICKS or MTU is reached with no interruptions in in_v, 
   packed is queued and an entry in fifo_queue_ram is added. 
   Each entry contains info necessary for server and tx module to send user data:
     - present flag which indicates that the packet is unacked 
     - checksum for this payload
     - seq - start address for the packet in raw data buffer
     - length of the packet ecpressed in bytes
     - retransmit_timer - timer to retransmit unacked packets
     - retransmit_tries - times server has tried to retransmit the packet
*/
import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_tx_queue #(
	parameter integer MTU              = 1400,
	parameter integer RETRANSMIT_TICKS = 1000000,
	parameter integer RAM_DEPTH        = 10,
	parameter integer PACKETS_DEPTH    = 3,
	parameter integer WAIT_TICKS       = 20
)
(
	input   logic                 clk,
	input   logic                 rst,
	input   dev_t                 dev,
	
	input   logic [7:0]           in_d,
	input   logic                 in_v,
	output  logic                 cts,
	input   logic                 tx_busy,
	input   logic                 tx_done,
	input   logic [31:0]          rem_ack,
    output  logic [31:0]          seq,  // packet's seq
    input   logic [31:0]          isn,  // packet's seq
	output  logic [7:0]           data, //in. data addr queue_addr 
    input   logic [RAM_DEPTH-1:0] addr, //out.
    input   logic                 req, //out.
    output  logic                 val,  //in. packet ready in queue
    output  logic [15:0]          len,  // packet's len
    output  logic [31:0]          payload_checksum,
	
	output logic                  force_fin,
	input  logic                  connected,
	input  logic                  flush_queue,  
	output logic                  queue_flushed
);

tcp_pkt_t upd_pkt, upd_pkt_q, new_pkt, new_pkt_q;

logic [PACKETS_DEPTH-1:0] new_addr, upd_addr, upd_addr_prev;
logic [$clog2(MTU+1)-1:0] ctr;
logic [$clog2(WAIT_TICKS+1)-1:0] timeout;
logic [31:0] checksum;
logic [31:0] cur_seq, seq_diff;
logic [RAM_DEPTH-1:0] space_left;
logic [7:0] in_d_prev;
logic in_v_prev;
logic connected_prev;

logic fifo_rst, fsm_rst, upd_cts, load, upd, checksum_rst, checksum_odd;

// initial for (int i = 0; i < 2**PACKETS_DEPTH; i++) pkt_info[i] = '0;

tcp_data_queue #(
	.D (RAM_DEPTH),
	.W (8)
) tcp_data_queue_inst (
	.rst (fifo_rst),
	.clk (clk),

	.w_v (in_v),
	.w_d (in_d),
	.init_addr (isn[RAM_DEPTH-1:0]+1),
	.rd_addr (addr),
	.rem_ack (rem_ack),
	.space_left (space_left),
	.r_v (req),
	.r_q (data),

	.f (full),
	.e (empty)
);

always @ (posedge clk) begin
	if (rst) fifo_rst <= 1;
	else begin
		connected_prev <= connected;
		fifo_rst <= connected_prev != connected;
	end
end

// infor about packets is kept here
fifo_queue_ram #(PACKETS_DEPTH) fifo_queue_ram_inst (.*);

logic [PACKETS_DEPTH:0] new_ptr, free_ptr, diff, flush_ctr;
assign new_addr = new_ptr[PACKETS_DEPTH-1:0];

assign diff = new_ptr - free_ptr;
logic [31:0] rem_ack_prev;
logic ack_ovfl;
always @ (posedge clk) begin
	rem_ack_prev <= rem_ack;
	upd_cts <= load || fifo_rst || (val && !in_v) || (rem_ack_prev != rem_ack); // update cts 
	if (upd_cts) cts <= connected && !diff[PACKETS_DEPTH] && (space_left >= MTU); // && ((cur_seq - rem_ack) < 1000);
end

// write logic
logic load_pend;
assign load_pend = (ctr == MTU || ((timeout == WAIT_TICKS-1) && ctr != 0));
always @ (posedge clk) begin
	if (fifo_rst) begin
		ctr          <= 0;
		new_ptr      <= 0;
		load         <= 0;
		timeout      <= 0;
		cur_seq      <= isn+1;
	end
	else begin
		if (in_v && !flush_queue) begin
			cur_seq <= cur_seq + 1; // increment sequence number each new byte. this number is local to module
			timeout <= 0; // force timeout counter to 0 when new data is coming
			ctr <= ctr + 1; // increment byte count
			load <= 0;
		end
		else if (load_pend) begin // If current block reaches MTU or transmit wait timer is done
		 	new_pkt.checksum <= checksum; // load checksum
			new_pkt.seq <= cur_seq - ctr; // load start addr
			new_pkt.exp_ack <= cur_seq; // load start addr
			new_pkt.length <= ctr; // length equals byte count for current packet. together with seq logic reads out facket from fifo
			new_pkt.present <= 1; // this packet is valid in memory
			new_pkt.retransmit_timer <= RETRANSMIT_TICKS; // preload so packet is read out asap the first time
			new_pkt.retransmit_tries <= 0;
			timeout <= timeout + 1; // increment timeout ctr to get out of this if branch
			ctr <= 0; // reset current packet byte count
			load <= 1; // queue the packet
		end
		else begin
			timeout <= (timeout == WAIT_TICKS) ? timeout : timeout + 1; // if fifo isn't empty and timer haven't reached timeout, increment timer
			load <= 0;
		end
		if (load) new_ptr <= new_ptr + 1; // increment address of stored packet
	end
end

// checksum calculation for queued packets
always @ (posedge clk) begin
	in_d_prev <= in_d;
	in_v_prev <= in_v;
end

assign checksum_rst = load || fifo_rst;

always @ (posedge clk) begin
	if (checksum_rst) begin
		checksum <= 0;
		checksum_odd <= 0;
	end
	else begin
		if (in_v) begin
			checksum_odd <= ~checksum_odd;
			if (checksum_odd) checksum <= checksum + {in_d_prev, in_d};
		end
		else if (checksum_odd && in_v_prev) begin
			checksum <= checksum + {in_d_prev, 8'h0};
		end
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
// retransmissions

assign payload_checksum = upd_pkt_q.checksum;
assign seq              = upd_pkt_q.seq;
assign len              = upd_pkt_q.length;

logic free;
logic retrans;
logic [$clog2(RETRANSMIT_TICKS+1)-1:0] retransmit_timer;

always @ (posedge clk) begin
	if (fsm_rst || rst) begin
		fsm <= queue_scan_s;
		upd <= 0;
		upd_addr <= 0;
		force_fin <= 0;
		val <= 0;
		free_ptr <= 0;
		flush_ctr <= 0;
		fsm_rst <= 0;
		queue_flushed <= 0;
	end
	else begin
		// don't change these fields:
		upd_pkt.checksum <= upd_pkt_q.checksum;
		upd_pkt.seq      <= upd_pkt_q.seq;
		upd_pkt.exp_ack  <= upd_pkt_q.exp_ack;
		upd_pkt.length   <= upd_pkt_q.length;
		upd_addr_prev <= upd_addr;
		case (fsm)
			queue_scan_s : begin
				upd <= 0;
				queue_flushed <= 0;
				// Continiously scan for unacked packets. If present flag found, check if it's acked (queue_check_s)
				 // if packet at current address is not present, read next
				if (flush_queue) fsm <= queue_flush_s;
				else if (upd_pkt_q.present && !load_pend) begin
					fsm <= queue_read_s;
 					upd_addr <= upd_addr_prev;
				end
				else upd_addr <= upd_addr + 1;
				seq_diff <= upd_pkt_q.exp_ack - rem_ack; // seq_ack_diff[31] means either ack or exp ack ovfl
				retransmit_timer <= upd_pkt_q.retransmit_timer;
				free <= 0;
				retrans <= 0;
			end
			queue_read_s : begin
				fsm <= queue_check_s;
				if (seq_diff[31]) free <= 1;
				else if (!seq_diff[31] && (retransmit_timer == RETRANSMIT_TICKS)) retrans <= 1;
			end
			queue_check_s : begin
				if (!tx_busy) begin
					upd <= 1;
					// transmit next segment. also in
					if (free) begin
						free_ptr <= free_ptr + 1;
						fsm <= queue_next_s;
						upd_pkt.present <= 0;
						upd_pkt.retransmit_timer <= 0;
						upd_pkt.retransmit_tries <= 0;
						val <= 0;
					end
					else if (retrans) begin 
						fsm <= queue_retrans_s;
						if (upd_pkt_q.retransmit_tries == 3) force_fin <= 1;
						upd_pkt.present <= 1;
						upd_pkt.retransmit_timer <= 0;
						upd_pkt.retransmit_tries <= upd_pkt_q.retransmit_tries + 1;
						val <= 1;
					end
					// clear present flag if acked
					else begin
						fsm <= queue_next_s;
						upd_pkt.present <= 1;
						upd_pkt.retransmit_timer <= upd_pkt_q.retransmit_timer + 1;
					// increment retransmit timer
						upd_pkt.retransmit_tries <= upd_pkt_q.retransmit_tries;
						val <= 0;
					end
				end
			end
			queue_next_s : begin
				upd <= 0;
				upd_addr_prev <= upd_addr + 1;
				upd_addr <= upd_addr + 1;
				fsm <= queue_wait_s;
			end
			queue_wait_s : begin
				fsm <= queue_scan_s;
			end
			//queue_wait2_s : begin
			//	fsm <= queue_scan_s;
			//end
			queue_retrans_s : begin
				upd <= 0;
				// if (upd) 
				if (tx_done) begin
					fsm <= queue_scan_s;
					val <= 0;
					upd_addr <= upd_addr + 1;
				end
				// if (!tx_busy && !val) / packet sent
			end
			queue_flush_s : begin
				val <= 0;
				upd_addr <= upd_addr + 1;
				upd_pkt.present <= 0;
				upd <= 1;
				flush_ctr <= flush_ctr + 1;
				if (flush_ctr == 0 && upd) begin
					queue_flushed <= 1;
					fsm_rst <= 1;
				end
			end
			default : begin
				force_fin <= 1;
				upd <= 0;
				val <= 0;
				fsm <= queue_scan_s;
				upd_pkt.present <= 0;
				upd_pkt.retransmit_timer <= 0;
				upd_pkt.retransmit_tries <= 0;
			end
		endcase
	end
end

endmodule : tcp_tx_queue

module fifo_queue_ram #(
	parameter DEPTH = 8
)
(
	input  logic     clk,
	input  logic     load,
	input  logic     upd,
	input  tcp_pkt_t new_pkt,
	output tcp_pkt_t new_pkt_q,
	input  tcp_pkt_t upd_pkt,
	output tcp_pkt_t upd_pkt_q,
	input  logic [DEPTH-1:0] new_addr,
	input  logic [DEPTH-1:0] upd_addr
);

tcp_pkt_t pkt_info [0:2**(DEPTH)-1];
// initial pkt_info = 0;

initial for (int i = 0; i < 2**DEPTH; i = i + 1) pkt_info[i] = '0;

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
	input  logic [D-1:0] init_addr,
	output logic [D-1:0] space_left,
	input  logic [D-1:0] rd_addr, // address to read from 
	input  logic [31:0]  rem_ack, // free bytes when ack received
	input  logic         r_v,
	output logic [W-1:0] r_q,
	
	output logic         f,
	output logic         e
);

logic [D-1:0] wr_addr;
logic [D:0]   diff;
logic [D:0]   wr_ctr;
logic [D:0]   rd_ctr;

assign diff = wr_ctr - rd_ctr;
assign space_left = (diff[D]) ? 0 : ~diff[D-1:0];

assign e = (diff == 0);
assign f = (diff[D] == 1);

always @ (posedge clk or posedge rst) begin // todo: sync reset
	if (rst) wr_ctr[D:0] <= {1'b0, (init_addr[D-1:0])}; // +1 because ACK will come with incremented '1' during 3whs 
	else if (w_v && !f) wr_ctr <= wr_ctr + 1;
end

assign wr_addr[D-1:0] = wr_ctr[D-1:0];

always @ (posedge clk or posedge rst) begin // todo: sync reset
	if (rst) rd_ctr[D:0] <= {1'b0, init_addr[D-1:0]};
	// else if (r_v && !e && (rd_ctr[D-1:0] == rd_addr)) rd_ctr <= rd_ctr + 1;
	else rd_ctr <= rem_ack[D:0];
end

reg [W-1:0] mem[(1<<D)-1:0];

int i;

//initial for (i = 0; i < 2**D; i = i + 1) mem[i] = '0;

always @ (posedge clk) r_q <= mem[rd_addr];

always @ (posedge clk) if (w_v && !f) mem[wr_addr] <= w_d;

endmodule : tcp_data_queue
