
import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_server #(
  parameter integer CONNECTION_TIMEOUT_TICKS = 10000000,
  parameter integer ACK_TIMEOUT              = 125000,
  parameter integer KEEPALIVE_PERIOD         = 125000000,
  parameter         ENABLE_KEEPALIVE         = 1'b1,
  parameter integer KEEPALIVE_TRIES          = 5
)
(
  input logic        clk,
  input logic        rst,
  input dev_t        dev,
  input port_t       port,
  output tcb_t       tcb,
  tcp.in             rx,
  tcp.out            tx,
  output logic       vout,
  output logic [7:0] dout,

  input  logic [31:0] queue_seq,
  input  logic        queue_pend,
  input  logic [15:0] queue_len,
  input  logic [31:0] queue_cs,
  output logic        flush_queue,
  input  logic        queue_flushed,
  output logic        connected,
  input  logic        connect, 
  input  logic        listen,  
  input  ipv4_t       rem_ipv4,
  input  port_t       rem_port,
  input  logic        force_fin
);

// Locally defined types
enum logic [2:0] {
  close_active,
  close_passive,
  close_reset
} close;

enum logic {
  tcp_client,
  tcp_server
} connection_type;

logic [31:0] prbs_reg;
logic [31:0] prbs;
logic prbs_val;

tcp_srv_fsm_t tcp_fsm;

logic [$clog2(CONNECTION_TIMEOUT_TICKS+1)-1:0] connection_timeout;
logic [$clog2(ACK_TIMEOUT+1)-1:0] ack_timer;
logic [$clog2(KEEPALIVE_PERIOD+1)-1:0] keepalive_timer;
logic [$clog2(KEEPALIVE_TRIES+1)-1:0] keepalive_tries;

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
// set tcp options
assign tx.tcp_opt_hdr.tcp_opt_sack_perm.sack_perm_pres = 0;
assign tx.tcp_opt_hdr.tcp_opt_sack.sack_pres           = 0;
assign tx.tcp_opt_hdr.tcp_opt_sack.sack_blocks         = 0;
assign tx.tcp_opt_hdr.tcp_opt_sack.block_pres          = 4'b0000;
assign tx.tcp_opt_hdr.tcp_opt_sack.sack[3:0]           = 0;
assign tx.tcp_opt_hdr.tcp_opt_timestamp.timestamp_pres = 0;

logic [7:0] rxd_reg;
logic       rxv_reg;

logic tcp_rst, fin_rst, force_ack, keepalive_ack, keepalive_fin;
logic last_ack_sent, active_fin_sent, passive_fin_sent, last_ack_received, tcb_created, conn_filter, valid_rx;

assign vout = rxv_reg && valid_rx;
assign dout = rxd_reg;
assign conn_filter = (rx.tcp_hdr_v && rx.tcp_hdr.dst_port == port && rx.tcp_hdr.src_port == tcb.port); // Indicate valid packed to open connection

always @ (posedge clk) tcp_rst <= rst || (connection_timeout == CONNECTION_TIMEOUT_TICKS) || fin_rst;

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
    valid_rx           <= 0;
    connection_type    <= tcp_client;
    force_ack          <= 0;
    keepalive_fin      <= 0;
    keepalive_tries    <= 0;
  end
  else begin
    rxv_reg <= rx.v;
    rxd_reg <= rx.d;
    if (!((tcp_fsm == tcp_closed_s) || (tcp_fsm == tcp_listen_s) || (tcp_fsm == tcp_established_s))) connection_timeout <= connection_timeout + 1;
    case (tcp_fsm)
      tcp_closed_s : begin
        flush_queue <= 0;
        tx.payload_length <= 0;
        if (listen) begin
          connection_type <= tcp_server;
          tcp_fsm <= tcp_listen_s;
        end
        else if (connect) begin
          connection_type <= tcp_client;
          tx.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
          tx.tcp_opt_hdr.tcp_opt_win.win      <= 8;
          tx.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
          tx.tcp_opt_hdr.tcp_opt_mss.mss      <= 8960;
          tx.ipv4_hdr.dst_ip <= rem_ipv4;
          tx.ipv4_hdr.id     <= 1; // *** todo: replace with PRBS
          tx.ipv4_hdr.length <= 20 + 28;
          tx.payload_chsum   <= 0;
          // set tcp header (syn)
          tx.tcp_hdr.tcp_offset   <= 7;
          tx.tcp_hdr.src_port     <= port;
          tx.tcp_hdr.dst_port     <= rem_port;
          tx.tcp_hdr.tcp_flags    <= 9'h002; // SYN
          tx.tcp_hdr.tcp_win_size <= 10;
          tx.tcp_hdr.tcp_chsum    <= 0;
          tx.tcp_hdr.tcp_pointer  <= 0;
          // create TCB for outcoming connection
          tcb_created      <= 1;
          tcb.ipv4_addr    <= rem_ipv4;
          tcb.port         <= rem_port;
          tcb.loc_ack_num  <= 0; // Set local ack to 0 before acquiring remote seq
          tcb.loc_seq_num  <= 32'habbadead; // *** todo: replace with PRBS
          if (tcb_created) begin
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
        if (rx.tcp_hdr_v && rx.tcp_hdr.tcp_flags.ack && rx.tcp_hdr.tcp_flags.syn && (rx.tcp_hdr.dst_port == port)) begin
          $display("%d.%d.%d.%d:%d:[SYN, ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
          dev.ipv4_addr[3],dev.ipv4_addr[2],dev.ipv4_addr[1],dev.ipv4_addr[0],port,
          rx.ipv4_hdr.src_ip[3],rx.ipv4_hdr.src_ip[2],rx.ipv4_hdr.src_ip[1],rx.ipv4_hdr.src_ip[0],
          rx.tcp_hdr.src_port,rx.tcp_hdr.tcp_seq_num,rx.tcp_hdr.tcp_ack_num
          );
        //  connected <= 1;
          tcp_fsm <= tcp_established_s;
          tx.ipv4_hdr.id     <= tx.ipv4_hdr.id + 1; // *** todo: replace with PRBS
          tx.ipv4_hdr.length <= 20 + 20;
          tx.payload_chsum   <= 0;
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
        tx.tcp_hdr.tcp_seq_num <= tcb.loc_seq_num;
        tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num;
        tx.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
        tx.tcp_opt_hdr.tcp_opt_win.win      <= 8;
        tx.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
        tx.tcp_opt_hdr.tcp_opt_mss.mss      <= 8960;
        if (rx.tcp_hdr_v && rx.tcp_hdr.tcp_flags.syn && (rx.tcp_hdr.dst_port == port)) begin // connection request
          // ipv4 header
          tx.ipv4_hdr.dst_ip <= rx.ipv4_hdr.src_ip;
          tx.ipv4_hdr.id     <= rx.ipv4_hdr.id;
          tx.ipv4_hdr.length <= 20 + 28;
          tx.payload_chsum   <= 0;
          // tcp header
          tx.tcp_hdr.tcp_offset    <= 7;
          tx.tcp_hdr.src_port      <= port;
          tx.tcp_hdr.dst_port      <= rx.tcp_hdr.src_port;
          tx.tcp_hdr.tcp_flags     <= 9'h012; // SYN ACK
          tx.tcp_hdr.tcp_win_size  <= 10;
          tx.tcp_hdr.tcp_chsum     <= 0;
          tx.tcp_hdr.tcp_pointer   <= 0;
          // create TCB for incoming connection
          tcb_created     <= 1;
          tcb.ipv4_addr   <= rx.ipv4_hdr.src_ip;
          tcb.port        <= rx.tcp_hdr.src_port;
          tcb.loc_ack_num <= rx.tcp_hdr.tcp_seq_num + 1; // Set local ack as remote seq + 1
          tcb.loc_seq_num <= 32'hfeadabba; // *** todo: replace with PRBS
          tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
          tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
        end
        if (tcb_created) begin // Once TCB fields are filled, continue
          $display("%d.%d.%d.%d:%d:[SYN] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], port,
            rx.ipv4_hdr.src_ip[3],rx.ipv4_hdr.src_ip[2],rx.ipv4_hdr.src_ip[1], rx.ipv4_hdr.src_ip[0],
            tcb.port, rx.tcp_hdr.tcp_seq_num, rx.tcp_hdr.tcp_ack_num);
          tx.tcp_hdr_v <= 1;
          tcp_fsm <= tcp_syn_received_s;
          tcb.isn <= tcb.loc_seq_num;
        end
        else tx.tcp_hdr_v <= 0;
      end
      tcp_syn_received_s : begin
        tx.payload_length     <= 0;
        tx.tcp_hdr_v          <= 0;
        tx.tcp_hdr.tcp_offset <= 5;
        if (rx.tcp_hdr_v && 
          (rx.tcp_hdr.tcp_flags.ack) &&
          (rx.tcp_hdr.dst_port == port) &&
          (rx.tcp_hdr.src_port == tcb.port) &&
          (rx.tcp_hdr.tcp_seq_num == tcb.rem_seq_num + 1)) begin
            $display("%d.%d.%d.%d:%d:[ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h. Connection established.",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], port,
		          rx.ipv4_hdr.src_ip[3],rx.ipv4_hdr.src_ip[2],rx.ipv4_hdr.src_ip[1], rx.ipv4_hdr.src_ip[0], rx.tcp_hdr.src_port,
              rx.tcp_hdr.tcp_seq_num, rx.tcp_hdr.tcp_ack_num);
            tcp_fsm <= tcp_established_s;
          //  connected <= 1;
            tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
            tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
            // tcb.loc_ack_num <= tcb.loc_ack_num;
            tcb.loc_seq_num <= rx.tcp_hdr.tcp_ack_num;
        end
      end
      tcp_established_s : begin
        connected <= 1;
        // tcp header
        tx.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 0;
        tx.tcp_opt_hdr.tcp_opt_win.win_pres <= 0;
        tx.tcp_hdr.tcp_offset               <= 5;
        tx.tcp_hdr.src_port                 <= port;
        tx.tcp_hdr.dst_port                 <= tcb.port;
        tx.tcp_hdr.tcp_win_size             <= 10;
        tx.tcp_hdr.tcp_chsum                <= 0;
        tx.tcp_hdr.tcp_pointer              <= 0;
        ////////////////////
        // transmit logic //
        ////////////////////
        if (queue_pend && !tx.busy) begin // if queue has something
          tcb.loc_seq_num        <= queue_seq + queue_len;
          tx.payload_chsum       <= queue_cs;
          tx.payload_length      <= queue_len;
          tx.ipv4_hdr.dst_ip     <= tcb.ipv4_addr;
          tx.ipv4_hdr.length     <= 20 + 20 + queue_len; // 20 for tcp header, 20 for ipv4 header
          tx.tcp_hdr.tcp_seq_num <= queue_seq; // get seq number from queue
          tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num; // get local ack from TCB
          tx.tcp_hdr.tcp_flags   <= 9'h018; // PSH ACK
          tx.tcp_hdr_v           <= 1;
          if (!tx.tcp_hdr_v) $display("%d.%d.%d.%d:%d: Transmitting (seq:%h,len:%d,ack:%h)", 
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], port, queue_seq, queue_len, tcb.loc_ack_num);
        end
        else if ((keepalive_ack || force_ack) && !tx.busy) begin // If currently remote seq != local ack, force ack w/o data
          $display("%d.%d.%d.%d:%d: Ack timeout (seq:%h, ack:%h)",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], port, tcb.loc_seq_num, tcb.loc_ack_num);
          tx.ipv4_hdr.id         <= rx.ipv4_hdr.id + 1;
          tx.tcp_hdr.tcp_seq_num <= (keepalive_ack) ? tcb.loc_seq_num - 1 : tcb.loc_seq_num;
          tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num;
          tx.tcp_hdr.tcp_flags   <= 9'h010; // ACK
          tx.payload_chsum       <= 0;
          tx.ipv4_hdr.length     <= 40; // 20 for tcp header
          tx.payload_length      <= 0;
          tx.tcp_hdr_v           <= 1;
        end
        else tx.tcp_hdr_v <= 0;
        ////////////////////
        // receive  logic //
        ////////////////////
        if (conn_filter && rx.tcp_hdr.tcp_seq_num == tcb.loc_ack_num) begin
          $display("%d.%d.%d.%d:%d: received data from %d:%d:%d:%d:%d (seq:%h,len:%d,loc ack:%h",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0],
            port, rx.ipv4_hdr.src_ip[3], rx.ipv4_hdr.src_ip[2], rx.ipv4_hdr.src_ip[1], rx.ipv4_hdr.src_ip[0],
            rx.tcp_hdr.src_port, rx.tcp_hdr.tcp_seq_num, rx.payload_length, tcb.loc_ack_num + rx.payload_length);
          valid_rx <= 1;
          tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
          tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
          tcb.loc_ack_num <= tcb.loc_ack_num + (rx.payload_length);
          if (rx.payload_length != 0) ack_timer <= 0; // Exclude 0-length packets: avoid Keepalive lock
          keepalive_tries <= 0;
          keepalive_timer <= 0;
        end
        else begin
          if (!rx.v) valid_rx <= 0;
          // Handle timeouts for ACK
          ack_timer <= (ack_timer == ACK_TIMEOUT) ? ack_timer : ack_timer + 1; // hold timeout until new packet received
          keepalive_timer <= (keepalive_timer == KEEPALIVE_PERIOD) ? 0 : keepalive_timer + 1; // hold timeout until new packet received
          force_ack <= (ack_timer == ACK_TIMEOUT - 1);
          keepalive_ack <= (keepalive_timer == KEEPALIVE_PERIOD - 1);
          if (keepalive_ack) keepalive_tries <= keepalive_tries + 1;
          if (keepalive_tries == KEEPALIVE_TRIES)  keepalive_fin <= 1;
        end
        //////////////////////
        // disconnect logic //
        //////////////////////
        // user-intiated disconnect or retransmissions failed for RETRANSMISSION_TRIES will close connection via active-close route
        if (keepalive_fin || force_fin || ((connection_type == tcp_client) && !connect) || ((connection_type == tcp_server) && !listen)) begin
          flush_queue <= 1;
          close <= close_active;
        end
        // if remote side wishes to close connection, go with passive close
        else if (conn_filter && rx.tcp_hdr.tcp_flags.fin) begin 
          flush_queue <= 1;
          close <= close_passive;
        end
		    // if rst flag received, skip connection termination
        else if (conn_filter && rx.tcp_hdr.tcp_flags.rst) begin
          flush_queue <= 1;
          close <= close_reset;
        end
        // either way, memory in tx queue should be flushed because RAM contents can't be simply reset
		    // it is necessary to flush it for future connections
        // So wait till queue is flushed...
        if (queue_flushed) begin
          case (close)
            close_active  : tcp_fsm <= tcp_send_fin_s;
            close_passive : tcp_fsm <= tcp_send_ack_s;
            close_reset   : fin_rst <= 1;
          endcase
        end
      end
      tcp_send_fin_s : begin
        tx.payload_length <= 0;
        tx.payload_chsum <= 0;
        if (tx.tcp_hdr_v) begin
          active_fin_sent <= 1;
          tx.tcp_hdr_v <= 0;
        end
        else if (!tx.busy && !active_fin_sent) tx.tcp_hdr_v <= 1;
        tx.ipv4_hdr.dst_ip       <= tcb.ipv4_addr;
        tx.ipv4_hdr.length       <= 40;
        tx.tcp_hdr.src_port      <= port;
        tx.tcp_hdr.dst_port      <= tcb.port;
        tx.tcp_hdr.tcp_flags     <= 9'h011; // FIN ACK
        tx.tcp_hdr.tcp_seq_num   <= tcb.loc_seq_num;
        tx.tcp_hdr.tcp_ack_num   <= tcb.loc_ack_num;
        if (conn_filter && rx.tcp_hdr.tcp_flags.ack) last_ack_received <= 1;
        if (conn_filter && rx.tcp_hdr.tcp_flags.fin && last_ack_received) tcp_fsm <= tcp_send_ack_s;
      end
      tcp_send_ack_s : begin
        tx.payload_length <= 0;
        tx.payload_chsum <= 0;
        if (tx.tcp_hdr_v) begin
          last_ack_sent <= 1;
          tcp_fsm <= tcp_last_ack_s;
          tx.tcp_hdr_v <= 0;
        end
        else if (!tx.busy && !last_ack_sent) tx.tcp_hdr_v <= 1;
        tx.ipv4_hdr.dst_ip     <= tcb.ipv4_addr;
        tx.ipv4_hdr.length     <= 40;
        tx.tcp_hdr.src_port    <= port;
        tx.tcp_hdr.dst_port    <= tcb.port;
        tx.tcp_hdr.tcp_flags   <= 9'h010; // ACK
        tx.tcp_hdr.tcp_seq_num <= tcb.loc_seq_num;
        tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num + 1;
      end
      tcp_last_ack_s : begin
        tx.payload_length <= 0;
        tx.payload_chsum <= 0;
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

endmodule : tcp_server
