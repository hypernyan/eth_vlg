
import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_server (
    input logic clk,
    input logic rst,
    input dev_t dev,
    ipv4.in     ipv4,
    output tcb_t tcb,
    tcp.in      rx, // raw tcp from parser
    tcp.out     tx, // muxed raw tcp to tx (from server or queue)
    
    input  logic [31:0] queue_seq,  // packet's seq
    input  logic        queue_val,  //in. packet ready in queue
    input  logic [15:0] queue_len,  // packet's len
    input  logic [31:0] queue_cs,  // packet's len
    output logic        flush_queue,  // packet's len
    input  logic        queue_flushed,  // packet's len
	output logic  connected,
	input  logic  connect, 
	input  logic  listen,  
	input  ipv4_t rem_ipv4,
	input  port_t rem_port,
	input  logic  force_fin
);

// Parameters

logic [31:0] prbs_reg;
logic [31:0] prbs;
logic prbs_val;

parameter integer ACK_TIMEOUT = 12500000;
// server related
tcp_srv_fsm_t tcp_fsm;

logic [7:0] in_d_prev;
logic in_v_prev;
logic read;
logic [$clog2(ACK_TIMEOUT)-1:0] ack_timer;
logic tcb_created;

// server state machine
// these values are fixed
assign tx.ipv4_hdr.src_ip = dev.ipv4_addr;
assign tx.ipv4_hdr.qos    = 0;
assign tx.ipv4_hdr.ver    = 4;
assign tx.ipv4_hdr.proto  = TCP; // 6
assign tx.ipv4_hdr.df     = 1;
assign tx.ipv4_hdr.mf     = 0;
assign tx.ipv4_hdr.ihl    = 5;
assign tx.ipv4_hdr.ttl    = 64; // default TTL
assign tx.ipv4_hdr.fo     = 0;
assign tx.ipv4_hdr.zero   = 0;
// set tcp options (no options currently)
//assign tx.tcp_opt_hdr.tcp_opt_mss.mss_pres             = 0;
//assign tx.tcp_opt_hdr.tcp_opt_mss.mss                  = 0;
//assign tx.tcp_opt_hdr.tcp_opt_win.win_pres             = 0;
//assign tx.tcp_opt_hdr.tcp_opt_win.win                  = 0;
assign tx.tcp_opt_hdr.tcp_opt_sack_perm.sack_perm_pres = 0;
assign tx.tcp_opt_hdr.tcp_opt_sack.sack_pres           = 0;
assign tx.tcp_opt_hdr.tcp_opt_sack.sack_blocks         = 0;
assign tx.tcp_opt_hdr.tcp_opt_sack.block_pres          = 4'b0000;
assign tx.tcp_opt_hdr.tcp_opt_sack.sack[3:0]           = 0;
assign tx.tcp_opt_hdr.tcp_opt_timestamp.timestamp_pres = 0;
parameter CONNECTION_TIMEOUT_TICKS = 10000000;
logic [$clog2(CONNECTION_TIMEOUT_TICKS+1)-1:0] connection_timeout;
logic tcp_rst;
logic fin_rst;
always @ (posedge clk) tcp_rst <= rst || (connection_timeout == CONNECTION_TIMEOUT_TICKS) || fin_rst;

logic rxv_flag, valid_rx;

tcp_hdr_t   rx_tcp_hdr;
logic [7:0] rx_d;
logic       rx_v;
assign rx_tcp_hdr = rx.tcp_hdr;
assign rx_d = rx.d;
assign rx_v = rx.v;
logic rx_tcp_hdr_v;
logic last_ack_sent, active_fin_sent, passive_fin_sent, last_ack_received;
assign rx_tcp_hdr_v = rx.tcp_hdr_v;

logic acive_close, conn_filter;
enum logic [2:0] {
	close_active,
	close_passive,
	close_reset
} close;

always @ (posedge clk) begin
    if (tcp_rst) begin
        tcp_fsm <= tcp_closed_s;
        tx.tcp_hdr         <= '0;
        tx.tcp_hdr_v       <= 0;
		tcb                <= '0;
		ack_timer          <= 0;
		tcb_created        <= 0;
		connected          <= 0;
		connection_timeout <= 0;
		last_ack_sent      <= 0;
		active_fin_sent    <= 0;
		passive_fin_sent   <= 0;
		last_ack_received  <= 0;
		fin_rst            <= 0;
		flush_queue        <= 0;
    end
    else begin
		if (!((tcp_fsm == tcp_closed_s) || (tcp_fsm == tcp_listen_s) || (tcp_fsm == tcp_established_s))) connection_timeout <= connection_timeout + 1;
        case (tcp_fsm)
            tcp_closed_s : begin
				flush_queue <= 0;
				tx.payload_length <= 0;
				if (listen) tcp_fsm <= tcp_listen_s;
				else if (connect) begin
					tx.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
					tx.tcp_opt_hdr.tcp_opt_win.win      <= 8;
					tx.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
					tx.tcp_opt_hdr.tcp_opt_mss.mss      <= 8960;
					tx.ipv4_hdr.dst_ip <= rem_ipv4;
				    tx.ipv4_hdr.id     <= 123; // *** todo: replace with PRBS
				    tx.ipv4_hdr.length <= 20 + 28;
				    tx.payload_checksum  <= 0;
					// set tcp header (syn)
	                tx.tcp_hdr.tcp_offset    <= 7;
	                tx.tcp_hdr.src_port      <= dev.tcp_port;
	                tx.tcp_hdr.dst_port      <= rem_port;
                    tx.tcp_hdr.tcp_flags     <= 9'h002; // SYN
	                tx.tcp_hdr.tcp_win_size  <= 10;
	                tx.tcp_hdr.tcp_checksum  <= 0;
	                tx.tcp_hdr.tcp_pointer   <= 0;
					// create TCB for outcoming connection
					tcb_created      <= 1;
					tcb.ipv4_addr    <= rem_ipv4;
					tcb.port         <= rem_port;
					tcb.loc_ack_num  <= 0; // Set local ack to 0 before acquiring remote seq
					tcb.loc_seq_num  <= 32'h12340000; // *** todo: replace with PRBS
					if (tcb_created) begin
					    //$display("%d.%d.%d.%d:%d: [SYN] to %d.%d.%d.%d:%d Seq=%h Ack=%h",
                        //	dev.ipv4_addr[3],
                        //	dev.ipv4_addr[2],
                        //	dev.ipv4_addr[1],
                        //	dev.ipv4_addr[0],
                        //	dev.tcp_port,
						//	rem_ipv4[3],
                        //	rem_ipv4[2],
                        //	rem_ipv4[1],
                        //	rem_ipv4[0],
						//	rem_port,
						//	tcb.loc_seq_num,
						//	tcb.loc_ack_num
                    	//);
						tx.tcp_hdr_v <= 1;
						tcp_fsm <= tcp_wait_syn_ack_s;
						tx.tcp_hdr.tcp_seq_num <= tcb.loc_seq_num;
	                	tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num;
					end
					else tx.tcp_hdr_v <= 0;
				end
            end
			tcp_wait_syn_ack_s : begin
				tx.tcp_hdr.tcp_offset <= 5;
				tx.payload_length <= 0;
				if (rx.tcp_hdr_v && rx.tcp_hdr.tcp_flags.ack && rx.tcp_hdr.tcp_flags.syn && (rx.tcp_hdr.dst_port == dev.tcp_port)) begin
                    $display("%d.%d.%d.%d:%d:[SYN, ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
                        dev.ipv4_addr[3],dev.ipv4_addr[2],dev.ipv4_addr[1],dev.ipv4_addr[0],dev.tcp_port,
						ipv4.ipv4_hdr.src_ip[3],ipv4.ipv4_hdr.src_ip[2],ipv4.ipv4_hdr.src_ip[1],ipv4.ipv4_hdr.src_ip[0],
						rx.tcp_hdr.src_port,rx.tcp_hdr.tcp_seq_num,rx.tcp_hdr.tcp_ack_num
                    );
					connected <= 1;
                    tcp_fsm <= tcp_established_s;
				    tx.ipv4_hdr.id       <= tx.ipv4_hdr.id + 1; // *** todo: replace with PRBS
				    tx.ipv4_hdr.length   <= 20 + 20;
				    tx.payload_checksum  <= 0;
					// set tcp header (ack)
                    tx.tcp_hdr.tcp_flags <= 9'h010; // ACK
	          		tx.tcp_hdr.tcp_seq_num <= tcb.loc_seq_num + 1;
	            	tx.tcp_hdr.tcp_ack_num <= rx.tcp_hdr.tcp_seq_num + 1;
					tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
					tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
					tcb.loc_ack_num <= rx.tcp_hdr.tcp_seq_num + 1;
					tcb.loc_seq_num <= tcb.loc_seq_num + 1;
					tcb.port        <= rx.tcp_hdr.src_port;
					tx.tcp_hdr_v    <= 1;
                end
				else tx.tcp_hdr_v <= 0;
			end
            tcp_listen_s : begin
				tx.payload_length <= 0;
				tx.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
				tx.tcp_opt_hdr.tcp_opt_win.win      <= 8;
				tx.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
				tx.tcp_opt_hdr.tcp_opt_mss.mss      <= 8960;
                if (rx.tcp_hdr_v && rx.tcp_hdr.tcp_flags.syn && (rx.tcp_hdr.dst_port == dev.tcp_port)) begin // connection request
  					// set ipv4 header
				    tx.ipv4_hdr.dst_ip <= rx.ipv4_hdr.src_ip;
				    tx.ipv4_hdr.id     <= rx.ipv4_hdr.id;
				    tx.ipv4_hdr.length <= 20 + 28;
				    tx.payload_checksum  <= 0;
					// set tcp header (syn + ack)
	                tx.tcp_hdr.tcp_offset    <= 7;
	                tx.tcp_hdr.src_port      <= dev.tcp_port;
	                tx.tcp_hdr.dst_port      <= rx.tcp_hdr.src_port;
                    tx.tcp_hdr.tcp_flags     <= 9'h012; // SYN ACK
	                tx.tcp_hdr.tcp_win_size  <= 10;
	                tx.tcp_hdr.tcp_checksum  <= 0;
	                tx.tcp_hdr.tcp_pointer   <= 0;
					// create TCB for incoming connection
					tcb_created <= 1;
					tcb.ipv4_addr   <= rx.ipv4_hdr.src_ip;
					tcb.port        <= rx.tcp_hdr.src_port;
					tcb.loc_ack_num <= rx.tcp_hdr.tcp_seq_num + 1; // Set local ack as remote seq + 1
					tcb.loc_seq_num <= 32'hfeadabba; // *** todo: replace with PRBS
					tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
					tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
                end
                if (tcb_created) begin
				    $display("%d.%d.%d.%d:%d:[SYN] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
				        dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], dev.tcp_port,
                        ipv4.ipv4_hdr.src_ip[3],ipv4.ipv4_hdr.src_ip[2],ipv4.ipv4_hdr.src_ip[1], ipv4.ipv4_hdr.src_ip[0],
                        rx.tcp_hdr.src_port, rx.tcp_hdr.tcp_seq_num, rx.tcp_hdr.tcp_ack_num);
					tx.tcp_hdr_v <= 1;
                    tcp_fsm <= tcp_syn_received_s;
					tcb.isn <= tcb.loc_seq_num;
				end
				else tx.tcp_hdr_v <= 0;
				tx.tcp_hdr.tcp_seq_num <= tcb.loc_seq_num;
	            tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num;
            end
            tcp_syn_received_s : begin
				tx.payload_length <= 0;

				tx.tcp_hdr_v <= 0;
				tx.tcp_hdr.tcp_offset <= 5;
                if (rx.tcp_hdr_v && 
				(rx.tcp_hdr.tcp_flags.ack) &&
				(rx.tcp_hdr.dst_port == dev.tcp_port) &&
				(rx.tcp_hdr.src_port == tcb.port) &&
				(rx.tcp_hdr.tcp_seq_num == tcb.rem_seq_num + 1)) begin
                    $display("%d.%d.%d.%d:%d:[ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h. Connection established.",
						dev.ipv4_addr[3],
                        dev.ipv4_addr[2],
                        dev.ipv4_addr[1],
                        dev.ipv4_addr[0],
                        dev.tcp_port,
                        ipv4.ipv4_hdr.src_ip[3],
                        ipv4.ipv4_hdr.src_ip[2],
                        ipv4.ipv4_hdr.src_ip[1],
                        ipv4.ipv4_hdr.src_ip[0],
                        rx.tcp_hdr.src_port,
                        rx.tcp_hdr.tcp_seq_num,
                        rx.tcp_hdr.tcp_ack_num
                    );
                    tcp_fsm <= tcp_established_s;
					connected <= 1;
					tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
					tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
					// tcb.loc_ack_num <= tcb.loc_ack_num;
					tcb.loc_seq_num <= rx.tcp_hdr.tcp_ack_num;
                end
            end
            tcp_established_s : begin
				tx.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 0;
				tx.tcp_opt_hdr.tcp_opt_win.win_pres <= 0;
	            tx.tcp_hdr.tcp_offset <= 5;
				// tcp header
	            tx.tcp_hdr.src_port      <= dev.tcp_port;
	            tx.tcp_hdr.dst_port      <= tcb.port;
                tx.tcp_hdr.tcp_flags     <= 9'h018; // PSH ACK
	            tx.tcp_hdr.tcp_win_size  <= 10;
	            //tx.tcp_hdr.tcp_checksum  <= queue.payload_checksum;
	            tx.tcp_hdr.tcp_checksum  <= 0;
	            tx.tcp_hdr.tcp_pointer   <= 0;
				// transmit logic
				if (queue_val && !tx.busy) begin // if queue has something
					tx.payload_checksum <= queue_cs;
					tx.payload_length <= queue_len;
					tx.ipv4_hdr.dst_ip <= tcb.ipv4_addr;
					tx.ipv4_hdr.length <= 20 + 20 + queue_len; // 20 for tcp header
	          		tx.tcp_hdr.tcp_seq_num <= queue_seq; // get seq number from queue
	            	tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num; // get local ack from TCB
					tx.tcp_hdr_v <= 1;
					tcb.loc_seq_num <= queue_seq + queue_len;
					if (!tx.tcp_hdr_v) $display("%d.%d.%d.%d:%d: Queue has data. Starting transmission (seq:%h, ack:%h)", 
						dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], dev.tcp_port, queue_seq, tcb.loc_ack_num);
				end
				else if (ack_timer == ACK_TIMEOUT-1 && tcb.rem_seq_num != tcb.loc_ack_num && !tx.busy) begin // If currently local seq != remote ack, force ack w/o data
					$display("%d.%d.%d.%d:%d: Ack timeout (seq:%h, ack:%h)",
						dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], dev.tcp_port, tcb.loc_seq_num, tcb.loc_ack_num);
					tx.ipv4_hdr.id <= rx.ipv4_hdr.id + 1;
					tx.tcp_hdr_v <= 1;
	          		tx.tcp_hdr.tcp_seq_num <= tcb.loc_seq_num;
	            	tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num;
					tx.payload_checksum    <= 0;
					tx.ipv4_hdr.length     <= 40; // 20 for tcp header
					tx.payload_length <= 0;
				end
				else begin
					tx.tcp_hdr_v <= 0;
				end
				// receive logic
                if (conn_filter && rx.tcp_hdr.tcp_seq_num == tcb.loc_ack_num) begin
                    $display("%d.%d.%d.%d:%d: received data from %d:%d:%d:%d:%d Seq=%h Ack=%h of length %d.",
						dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0],
						dev.tcp_port,ipv4.ipv4_hdr.src_ip[3], ipv4.ipv4_hdr.src_ip[2], ipv4.ipv4_hdr.src_ip[1], ipv4.ipv4_hdr.src_ip[0],
						rx.tcp_hdr.src_port, rx.tcp_hdr.tcp_seq_num, rx.tcp_hdr.tcp_ack_num, rx.ipv4_hdr.length - 40
                    );
					tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
					tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
					tcb.loc_ack_num <= tcb.loc_ack_num + (rx.ipv4_hdr.length - 40);
					valid_rx <= 1;
					ack_timer <= 0;
                end
				else begin
					if (!rx.v) valid_rx <= 0;
					ack_timer <= (ack_timer == ACK_TIMEOUT) ? ack_timer : ack_timer + 1; // hold timeout until new packet received
				end
				// retransmissions failed for RETRANSMISSION_TRIES will close connection via active-close route
				if (force_fin) begin
					flush_queue <= 1;
					close <= close_active;
				end
				else if (conn_filter && rx.tcp_hdr.tcp_flags.fin) begin // if remote side wishes to close connection, go with passive close.
					flush_queue <= 1;
					close <= close_passive;
				end
				else if (conn_filter && rx.tcp_hdr.tcp_flags.rst) begin
					flush_queue <= 1;
					close <= close_reset;
				end
				// either way, memory in tx queue should be flushed because RAM can't be simply reset
				else if (queue_flushed) begin
					case (close)
						close_active  : tcp_fsm <= tcp_send_fin_s;
						close_passive : tcp_fsm <= tcp_send_ack_s;
						close_reset   : fin_rst <= 1;
					endcase
				end
			end
			tcp_send_fin_s : begin
				tx.payload_length <= 0;
				tx.payload_checksum <= 0;
				if (tx.tcp_hdr_v) begin
					active_fin_sent <= 1;
					tx.tcp_hdr_v <= 0;
				end
				else if (!tx.busy && !active_fin_sent) tx.tcp_hdr_v <= 1;
				tx.ipv4_hdr.dst_ip       <= tcb.ipv4_addr;
				tx.ipv4_hdr.length       <= 40;
				tx.tcp_hdr.src_port      <= dev.tcp_port;
	    	    tx.tcp_hdr.dst_port      <= tcb.port;
				tx.tcp_hdr.tcp_flags     <= 9'h011; // FIN ACK
				tx.tcp_hdr.tcp_seq_num   <= tcb.loc_seq_num;
				tx.tcp_hdr.tcp_ack_num   <=  tcb.loc_ack_num;
				if (conn_filter && rx.tcp_hdr.tcp_flags.ack) last_ack_received <= 1;
				if (conn_filter && rx.tcp_hdr.tcp_flags.fin && last_ack_received) tcp_fsm <= tcp_send_ack_s;
			end
			tcp_send_ack_s : begin
				tx.payload_length <= 0;
				tx.payload_checksum <= 0;
				if (tx.tcp_hdr_v) begin
					last_ack_sent <= 1;
					tcp_fsm <= tcp_last_ack_s;
					tx.tcp_hdr_v <= 0;
				end
				else if (!tx.busy && !last_ack_sent) tx.tcp_hdr_v <= 1;
				tx.ipv4_hdr.dst_ip     <= tcb.ipv4_addr;
				tx.ipv4_hdr.length     <= 40;
				tx.tcp_hdr.src_port    <= dev.tcp_port;
	    	    tx.tcp_hdr.dst_port    <= tcb.port;
				tx.tcp_hdr.tcp_flags   <= 9'h010; // ACK
				tx.tcp_hdr.tcp_seq_num <= tcb.loc_seq_num;
				tx.tcp_hdr.tcp_ack_num <=  tcb.loc_ack_num + 1;
			end
            tcp_last_ack_s : begin
				tx.payload_length <= 0;
				tx.payload_checksum <= 0;
				if (tx.tcp_hdr_v) begin
					passive_fin_sent <= 1;
					tx.tcp_hdr_v <= 0;
				end
				else if (!tx.busy && !passive_fin_sent) tx.tcp_hdr_v <= 1;
				tx.tcp_hdr.tcp_flags   <= 9'h011; // FIN ACK
				tx.tcp_hdr.tcp_seq_num <= tcb.loc_seq_num;
				tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num + 1;
				if (conn_filter && rx.tcp_hdr.tcp_flags.ack) fin_rst <= 1;
            end
        endcase
    end
end

assign conn_filter = (rx.tcp_hdr_v && rx.tcp_hdr.dst_port == dev.tcp_port && rx.tcp_hdr.src_port == tcb.port); // Indicate valid packed to open connection

endmodule : tcp_server
