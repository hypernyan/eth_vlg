import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_tx #(
parameter integer TX_QUEUE_DEPTH = 10
)(
	input logic clk,
	input logic rst,
	input dev_t dev,
	tcp.in      tcp,
	ipv4.out    tx,
	input  logic [7:0]                queue_data, //in. data addr queue_addr 
    output logic [TX_QUEUE_DEPTH-1:0] queue_addr, //out.
    output logic   req //out.
);

localparam MIN_TCP_HDR_LEN = 20;
localparam MAX_TCP_HDR_LEN = 60;
localparam HDR_OPTIONS_POS = 13;

ipv4_hdr_t tx_ipv4_hdr;
tcp_hdr_t tcp_hdr, cur_tcp_hdr;

logic [7:0] tx_d;
logic       tx_v;

logic fsm_rst;
logic [15:0] byte_cnt;
logic [0:MAX_TCP_HDR_LEN-1][7:0] hdr, hdr_calc;
logic transmitting;
logic hdr_done;
logic done, opt_assembled;

logic [31:0] pseudo_hdr_checksum, hdr_checksum;

logic calc, calc_done;
logic [0:39][7:0] opt_hdr;
logic [0:11][7:0] pseudo_hdr;
logic [19:0][7:0] tcp_tcp_hdr;

logic [31:0] checksum_carry;
logic [15:0] calc_byte_cnt;
logic [15:0] checksum;
logic tx_req;
assign tx_ipv4_hdr = tx.ipv4_hdr;
assign tx_d = tx.d;
assign tx_v = tx.v;
assign tx_sof = tx.sof;
assign tx_eof = tx.eof;

logic tcp_d;   
logic tcp_v;   
logic tcp_sof; 
logic tcp_eof; 
logic txv_reg; 
assign tcp_req   = tcp.req;
assign tcp_rdy   = tcp.rdy;
assign tcp_hdr_v = tcp.tcp_hdr_v;

assign tcp_hdr   = tcp.tcp_hdr;
assign tcp_d     = tcp.d;
assign tcp_v     = tcp.v;
assign tcp_sof   = tcp.sof;
assign tcp_eof   = tcp.eof;

assign tx.ipv4_hdr = tcp.ipv4_hdr;

logic [16:0] checksum_summ; // extra bit for sum's carry

assign checksum_summ[16:0] = checksum_carry[31:16] + checksum_carry[15:0]; // Calculate actual checksum
assign checksum = ~ (checksum_summ[15:0] + checksum_summ[16]);

logic [15:0] pseudo_hdr_pkt_len;
assign pseudo_hdr_pkt_len = (tcp.ipv4_hdr.length - 20);
always @ (posedge clk) begin
	if (fsm_rst) begin
		hdr            <= 0;
		hdr_done       <= 0;
		tx.eof <= 0;
		txv_reg        <= 0;
		transmitting   <= 0;
		byte_cnt       <= 0;
		pseudo_hdr_checksum <= 0;
		hdr_checksum   <= 0;
		calc           <= 0;
		calc_done      <= 0;
		calc_byte_cnt  <= 0;
		checksum_carry <= 0;
		tcp.req        <= 0;
		pseudo_hdr     <= 0;
		req            <= 0;
		cur_tcp_hdr    <= 0;
		queue_addr     <= 0;
	end
	else begin
		if (tcp.tcp_hdr_v) cur_tcp_hdr <= tcp.tcp_hdr;
		if (txv_reg) byte_cnt <= byte_cnt + 1; // count outcoming bytes
		tx.sof <= (calc_done && !transmitting); // assert sof when done calculating checksum 
		if (opt_assembled && !calc) begin // wait for options to be assembled, latch them for checksum calculation
			hdr_calc <= {cur_tcp_hdr, opt_hdr}; // concat header from tcp header and options
			pseudo_hdr <= {tcp.ipv4_hdr.src_ip, tcp.ipv4_hdr.dst_ip, 8'h0, TCP, pseudo_hdr_pkt_len}; // assemble pseudo header
			checksum_carry <= tcp.payload_checksum; // initialize checksum
			calc <= 1;
		end
		if (calc) begin // checksum is calculated here
			calc_byte_cnt <= calc_byte_cnt + 1;
			pseudo_hdr[0:9] <= pseudo_hdr[2:11]; // shift tcp header and options by 16 bits
			hdr_calc[0:MAX_TCP_HDR_LEN-3] <= hdr_calc[2:MAX_TCP_HDR_LEN-1];
			pseudo_hdr_checksum <= pseudo_hdr_checksum + pseudo_hdr[0:1];
			hdr_checksum <= hdr_checksum + hdr_calc[0:1]; // Actual calculation
			if (calc_byte_cnt == 6) checksum_carry <= checksum_carry + pseudo_hdr_checksum; // Pseudo header length is 12 bytes (6 ticks by 16 bits)
			else if (calc_byte_cnt == (cur_tcp_hdr.tcp_offset << 1)) begin // Header has variable length, calc takes variable amount of ticks
				checksum_carry <= checksum_carry + hdr_checksum;
				calc_done <= 1;
			end
		end
		if (calc_done && opt_assembled && !transmitting) begin
			//$display("<- srv: TCP tx from %d.%d.%d.%d:%d to %d.%d.%d.%d:%d",
			//	dev.ipv4_addr[3],
			//	dev.ipv4_addr[2],
			//	dev.ipv4_addr[1],
			//	dev.ipv4_addr[0],
			//	tcp.tcp_hdr.src_port,
			//	tcp.ipv4_hdr.dst_ip[3],
			//	tcp.ipv4_hdr.dst_ip[2],
			//	tcp.ipv4_hdr.dst_ip[1],
			//	tcp.ipv4_hdr.dst_ip[0],
			//	tcp.tcp_hdr.src_port
			//);
			//$display("<- srv: TCP tx flags:");
			//if (tcp.tcp_hdr.tcp_flags[8]) $display("NS");
			//if (tcp.tcp_hdr.tcp_flags[7]) $display("CWR");
			//if (tcp.tcp_hdr.tcp_flags[6]) $display("ECE");
			//if (tcp.tcp_hdr.tcp_flags[5]) $display("URG");
			//if (tcp.tcp_hdr.tcp_flags[4]) $display("ACK");
			//if (tcp.tcp_hdr.tcp_flags[3]) $display("PSH");
			//if (tcp.tcp_hdr.tcp_flags[2]) $display("RST");
			//if (tcp.tcp_hdr.tcp_flags[1]) $display("SYN");
			//if (tcp.tcp_hdr.tcp_flags[0]) $display("FIN");
			transmitting <= 1; // Start transmitting now
			txv_reg <= 1;
			// Assemble header to be transmitted
			hdr[0:1]     <= cur_tcp_hdr.src_port;
	        hdr[2:3]     <= cur_tcp_hdr.dst_port;
	        hdr[4:7]     <= cur_tcp_hdr.tcp_seq_num;
	        hdr[8:11]    <= cur_tcp_hdr.tcp_ack_num;
            hdr[12][7:4] <= cur_tcp_hdr.tcp_offset;
            {hdr[12][0], hdr[13][7:0]} <= cur_tcp_hdr.tcp_flags;
	        hdr[14:15]   <= cur_tcp_hdr.tcp_win_size;
	        hdr[16:17]   <= checksum;
	        hdr[18:19]   <= cur_tcp_hdr.tcp_pointer;
			hdr[MIN_TCP_HDR_LEN:MAX_TCP_HDR_LEN-1] <= opt_hdr;
		end
		else if (transmitting) hdr[0:MAX_TCP_HDR_LEN-2] <= hdr[1:MAX_TCP_HDR_LEN-1];
		if (transmitting && byte_cnt == ((cur_tcp_hdr.tcp_offset << 2) - 2) && tcp.payload_length != 0) begin
			req <= 1;
		end
		if (req) hdr_done <= 1;
		if (tcp.tcp_hdr_v) queue_addr <= tcp.tcp_hdr.tcp_seq_num;
		else if (req) queue_addr <= queue_addr + 1;
		if (tcp.ipv4_hdr.length - 22 == byte_cnt) tx.eof <= 1;
	end
end
always @ (posedge clk) tx.v <= txv_reg;
always @ (posedge clk) tx.d <= (hdr_done) ? queue_data : hdr[0]; // mux output between header and data from server

assign tcp.done = tx.done;
assign fsm_rst = (tx.eof || rst);

logic [4:0] opt_addr;
logic [3:0] sack_byte_cnt;
logic [1:0] sack_seg;
logic       timestamp_byte_cnt;
logic [7:0] tcp_sack_len;
tcp_opt_t   opt;

assign tcp_sack_len = (tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks << 3) + 2;

logic [0:14][31:0] opt_hdr_proto;
logic [0:14]       opt_hdr_pres;

logic cur_opt_pres, shift_opt, tcp_opt_done;
logic [3:0] opt_byte_cnt;
logic [3:0] opt_len_32;
logic busy;
assign tcp.busy = (busy || tx.busy);
always @ (posedge clk) begin
	if (fsm_rst) begin
		opt           <= tcp_opt_mss;
		opt_addr      <= 0;
		opt_byte_cnt  <= 0;
		opt_hdr_pres  <= 0;
		opt_hdr_proto <= 0;
		opt_len_32    <= 0;
		opt_assembled <= 0;
		shift_opt     <= 0;
		busy      <= 0;
	end
	else begin
		if (tcp.tcp_hdr_v) begin // transmit starts here
			busy <= 1;  // set busy flag and reset it when done transmitting. needed for server and queue to wait for sending next packet 
			shift_opt <= 1; // After options and header are set, compose a valid option header
			opt_hdr_proto <= {
				tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp.snd,
				tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp.rec,
				{TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_TIMESTAMP, 8'd10},
				tcp.tcp_opt_hdr.tcp_opt_sack.sack[3].right,
				tcp.tcp_opt_hdr.tcp_opt_sack.sack[3].left,
				tcp.tcp_opt_hdr.tcp_opt_sack.sack[2].right,
				tcp.tcp_opt_hdr.tcp_opt_sack.sack[2].left,
				tcp.tcp_opt_hdr.tcp_opt_sack.sack[1].right,
				tcp.tcp_opt_hdr.tcp_opt_sack.sack[1].left,
				tcp.tcp_opt_hdr.tcp_opt_sack.sack[0].right,
				tcp.tcp_opt_hdr.tcp_opt_sack.sack[0].left,
				{TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_SACK, tcp_sack_len},
				{TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_SACK_PERM, 8'd2},
				{TCP_OPT_NOP, TCP_OPT_WIN, 8'd3, tcp.tcp_opt_hdr.tcp_opt_win.win},
				{TCP_OPT_MSS, 8'd4, tcp.tcp_opt_hdr.tcp_opt_mss.mss[1], tcp.tcp_opt_hdr.tcp_opt_mss.mss[0]}
			}; // Option header prototype. Fill it with all possible options
			opt_hdr_pres <= {
				{3{tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp_pres}},
				{2{tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres && tcp.tcp_opt_hdr.tcp_opt_sack.block_pres[3]}},
				{2{tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres && tcp.tcp_opt_hdr.tcp_opt_sack.block_pres[2]}},
				{2{tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres && tcp.tcp_opt_hdr.tcp_opt_sack.block_pres[1]}},
				{2{tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres && tcp.tcp_opt_hdr.tcp_opt_sack.block_pres[0]}},
				tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres,
				tcp.tcp_opt_hdr.tcp_opt_sack_perm.sack_perm_pres,
				tcp.tcp_opt_hdr.tcp_opt_win.win_pres,
				tcp.tcp_opt_hdr.tcp_opt_mss.mss_pres
			}; // Set which option fields are present
		end
		else if (shift_opt) begin // create valid options to concat it with tcp header
			opt_byte_cnt <= opt_byte_cnt + 1;
			opt_hdr_proto[0:13] <= opt_hdr_proto[1:14];
			opt_hdr_pres[0:13] <= opt_hdr_pres[1:14];
			if (opt_hdr_pres[0]) begin // Shift by 32 bits
				opt_len_32 <= opt_len_32 + 1;
				opt_hdr[0:3] <= opt_hdr_proto[0];
				opt_hdr[4:39] <= opt_hdr[0:35];
			end
			if (opt_byte_cnt == 14) begin
				opt_assembled <= 1;
				shift_opt <= 0;
			end
		end
	end
end

assign opt_len = opt_len_32 << 2;

endmodule : tcp_vlg_tx
