import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_engine #(
  parameter int MTU                      = 1500,
  parameter int CONNECTION_TIMEOUT       = 10000000,
  parameter int ACK_TIMEOUT              = 125000,
  parameter int KEEPALIVE_PERIOD         = 600000000,
  parameter int KEEPALIVE_INTERVAL       = 125000000,
  parameter bit ENABLE_KEEPALIVE         = 1,
  parameter int KEEPALIVE_TRIES          = 5,
  parameter int DEFAULT_WINDOW_SIZE      = 1000,
  parameter bit VERBOSE                  = 0
)
(
  input logic  clk,
  input logic  rst,
  input dev_t  dev,

  tcp.in_rx    rx,
  tcp.out_tx   tx,

  tx_ctrl.out tx_ctrl,
  rx_ctrl.out rx_ctrl,
  tcp_ctrl.in ctrl
);

  assign tx_ctrl.req = tx.req;
  assign tx_ctrl.connected = ctrl.connected;
  assign rx_ctrl.connected = ctrl.connected;
  assign tx.strm = tx_ctrl.strm;

  // Locally defined types
  enum logic [3:0] {
    close_none,
    close_active,
    close_passive,
    close_reset
  } close;
  
  enum logic {
    tcp_client,
    tcp_server
  } con_type;

  enum logic [3:0] {
    tx_idle,
    tx_keepalive,
    tx_forced_ack,
    tx_payload
  } tx_type;

  enum logic [17:0] {
    closed_s,
    listen_s,

    con_send_syn_s,
    con_syn_sent_s,
    
    con_send_ack_s,
    con_ack_sent_s,
    
    con_send_syn_ack_s,
    con_syn_ack_sent_s,

    scl_s, 
    init_s, 

    established_idle_s,
    established_tx_s,

    flush_s,

    dcn_send_fin_s,
    dcn_fin_sent_s,

    dcn_send_ack_s,
    dcn_ack_sent_s,
    dcn_send_rst_s

  } fsm;

  tcb_t tcb;
  assign rx_ctrl.tcb = tcb;
  assign tx_ctrl.tcb = tcb;
  logic send_keepalive, keepalive_sent, keepalive_dcn;
  logic tcp_rst, fin_rst;
  logic last_ack_sent, active_fin_sent, passive_fin_sent, last_ack_rec;
  ipv4_vlg_pkg::id_t ipv4_id_prng;
  tcp_num_t seq_num_prng;

  logic tmr_con, tmr_rst_con, tmr_en_con, tmr_dcn, tmr_rst_dcn, tmr_en_dcn;

  prng #(.W (16), .POLY(16'hbeef)) prng_ipv4_id_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (ipv4_id_prng)
  );

  prng #(.W (32), .POLY(32'hdeadbeef)) prng_seq_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (seq_num_prng)
  );

  eth_vlg_tmr #(
    .TICKS (CONNECTION_TIMEOUT),
    .AUTORESET (1))
  con_tmr_inst (  
    .clk (clk),
    .rst (tmr_rst_con),
    .en  (tmr_en_con),
    .tmr (tmr_con)
  );

  eth_vlg_tmr #(
    .TICKS (CONNECTION_TIMEOUT),
    .AUTORESET (1))
  dcn_tmr_inst (  
    .clk (clk),
    .rst (tmr_rst_dcn),
    .en  (tmr_en_dcn),
    .tmr (tmr_dcn)
  );

  always @ (posedge clk) begin
    if (rst) tcp_rst <= 1;
    else tcp_rst <= tmr_con || tmr_dcn || fin_rst;
  end

  tcp_scl_t scl_raw, scl_ctr;   // raw window scale (max is 14)

  assign rem_port_flt = rx.meta.val && (rx.meta.tcp_hdr.src_port == tcb.rem_port);
  assign loc_port_flt = rx.meta.val && (rx.meta.tcp_hdr.dst_port == ctrl.loc_port);
  assign port_flt     = rx.meta.val && (rx.meta.tcp_hdr.src_port == tcb.rem_port) && (rx.meta.tcp_hdr.dst_port == tcb.loc_port);

  assign syn_rec     = loc_port_flt && rx.meta.tcp_hdr.tcp_flags == TCP_FLAG_SYN;
  assign syn_ack_rec = loc_port_flt && rx.meta.tcp_hdr.tcp_flags.syn && rx.meta.tcp_hdr.tcp_flags.ack;
  assign ack_rec     =     port_flt && rx.meta.tcp_hdr.tcp_flags.ack && rx.meta.tcp_hdr.tcp_seq_num == tcb.rem_seq + 1;
  assign fin_rec     =     port_flt && rx.meta.tcp_hdr.tcp_flags.fin;
  assign rst_rec     =     port_flt && rx.meta.tcp_hdr.tcp_flags.rst;

  logic sent;
  always @ (posedge clk) begin
    if (tcp_rst) begin
      fsm              <= closed_s;
      close            <= close_none;
      con_type         <= tcp_client;
      tcb              <= '0;
      ctrl.connected   <= 0;
      tmr_en_con       <= 0;
      tmr_rst_con      <= 1;
      tmr_en_dcn       <= 0;
      tmr_rst_dcn      <= 1;
      last_ack_rec     <= 0;
      last_ack_sent    <= 0;
      active_fin_sent  <= 0;
      passive_fin_sent <= 0;
      keepalive_sent   <= 0;
      fin_rst          <= 0;
      tx.rdy           <= 0;
      tx.meta          <= 0;
      tx_type          <= tx_idle;
      rx_ctrl.init     <= 0;
      rx_ctrl.ack_sent <= 0;
      tx_ctrl.sent     <= 0;
      tx_ctrl.flush    <= 0;
      tx_ctrl.init     <= 0;
      sent             <= 0;
      tmr_en_con       <= 0;
      tmr_en_dcn       <= 0;
      scl_raw          <= 0;
      scl_ctr          <= 0;
    end
    else begin
      case (fsm)
        closed_s : begin
          tcb.scl         <= 1;
          tcb.win_scl     <= '1;
          tmr_rst_con     <= 0;
          tmr_rst_dcn     <= 0;
          tmr_en_con      <= 0;
          tmr_en_dcn      <= 0;
          tx_ctrl.flush   <= 0;
          tx.meta.pld_len <= 0;
          tx.meta.pld_cks <= 0;
          if (ctrl.listen) begin
            con_type <= tcp_server; // passive open (server)
            fsm      <= listen_s;
          end
          else if (ctrl.connect) begin
            con_type <= tcp_client; // active open
            fsm      <= con_send_syn_s;
          end
        end
        /////////////////
        // Active Open //
        /////////////////
        con_send_syn_s : begin
          tmr_en_con <= 1;
          if (VERBOSE) $display("%d.%d.%d.%d:%d-> [SYN] to %d.%d.%d.%d:%d Seq=%h Ack=%h",
            dev.ipv4_addr[3],dev.ipv4_addr[2],dev.ipv4_addr[1],dev.ipv4_addr[0],ctrl.loc_port,
            ctrl.rem_ipv4[3],ctrl.rem_ipv4[2],ctrl.rem_ipv4[1],ctrl.rem_ipv4[0],
            ctrl.rem_port, seq_num_prng, tcb.loc_ack
          );
          // create TCB for outcoming connection
          tcb.ipv4_addr     <= ctrl.rem_ipv4;
          tcb.rem_port      <= ctrl.rem_port;
          tcb.loc_port      <= ctrl.loc_port;
          tcb.loc_ack       <= 0; // Set local ack to 0 before acquiring remote seq
          tcb.loc_seq       <= seq_num_prng;
          tx.meta.mac_known <= 0;
          // Set options at connection establishment
          tx.meta.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
          tx.meta.tcp_opt_hdr.tcp_opt_win.win      <= 8;
          tx.meta.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
          tx.meta.tcp_opt_hdr.tcp_opt_mss.mss      <= MTU - 40;
          // Set relevant IP header fields
          tx.meta.ipv4_hdr.dst_ip <= ctrl.rem_ipv4;
          tx.meta.ipv4_hdr.id     <= ipv4_id_prng;
          tx.meta.ipv4_hdr.length <= 20 + 28;
          // set tcp header (syn)
          tx.meta.tcp_hdr.tcp_offset   <= 7;
          tx.meta.tcp_hdr.src_port     <= ctrl.loc_port;
          tx.meta.tcp_hdr.dst_port     <= ctrl.rem_port;
          tx.meta.tcp_hdr.tcp_flags    <= TCP_FLAG_SYN;
          tx.meta.tcp_hdr.tcp_win_size <= DEFAULT_WINDOW_SIZE;
          tx.meta.tcp_hdr.tcp_cks      <= 0;
          tx.meta.tcp_hdr.tcp_pointer  <= 0;
          tx.meta.tcp_hdr.tcp_seq_num  <= seq_num_prng;
          tx.meta.tcp_hdr.tcp_ack_num  <= 0;
          fsm <= con_syn_sent_s;
          tx.rdy <= 1;
        end
        con_syn_sent_s : begin
          if (tx.ack) tx.rdy <= 0; // release rdy after confirmation from tcp_tx
          if (syn_ack_rec) begin // when syn-ack received...
            if (VERBOSE) $display("%d.%d.%d.%d:%d<- [SYN, ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
              dev.ipv4_addr[3],dev.ipv4_addr[2],dev.ipv4_addr[1],dev.ipv4_addr[0],tcb.loc_port,
              rx.meta.ipv4_hdr.src_ip[3],rx.meta.ipv4_hdr.src_ip[2],rx.meta.ipv4_hdr.src_ip[1],rx.meta.ipv4_hdr.src_ip[0],
              rx.meta.tcp_hdr.src_port, rx.meta.tcp_hdr.tcp_seq_num, rx.meta.tcp_hdr.tcp_ack_num
            );
            tcb.rem_seq <= rx.meta.tcp_hdr.tcp_seq_num + 1; // fill in tcb fields 
            tcb.rem_ack <= rx.meta.tcp_hdr.tcp_ack_num;
            tcb.loc_seq <= tcb.loc_seq + 1;
            tcb.loc_ack <= rx.meta.tcp_hdr.tcp_seq_num + 1;
            scl_raw <= (rx.meta.tcp_opt_hdr.tcp_opt_win.win_pres) ? rx.meta.tcp_opt_hdr.tcp_opt_win.win : 1; // raw scaling option
            tcb.mac_addr <= rx.meta.mac_hdr.src_mac;
            tcb.mac_known <= 1;
            tx.meta.tcp_hdr.tcp_offset <= 5;
            fsm <= con_send_ack_s;
          end
        end
        con_send_ack_s : begin
          if (VERBOSE) $display("%d.%d.%d.%d:%d-> [ACK] to %d.%d.%d.%d:%d Seq=%h Ack=%h. Connection established",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
            tx.meta.ipv4_hdr.dst_ip[3], tx.meta.ipv4_hdr.dst_ip[2], tx.meta.ipv4_hdr.dst_ip[1], tx.meta.ipv4_hdr.dst_ip[0],
            tcb.rem_port, tcb.loc_seq, tcb.loc_ack
          );
          tx.meta.ipv4_hdr.id         <= tx.meta.ipv4_hdr.id + 1;
          tx.meta.ipv4_hdr.length     <= 20 + 20;
          tx.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_ACK; // ACK
          tx.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq;
          tx.meta.tcp_hdr.tcp_ack_num <= tcb.loc_ack;
          tx.meta.mac_hdr.dst_mac     <= tcb.mac_addr;
          tx.rdy                      <= 1;
          fsm                         <= con_ack_sent_s;
        end
        con_ack_sent_s : begin
          if (tx.ack) tx.rdy <= 0;
          if (tx.done) fsm <= scl_s;
        end
        //////////////////
        // Passive Open //
        //////////////////
        listen_s : begin
          if (syn_rec) begin // connection request
            if (VERBOSE) $display("%d.%d.%d.%d:%d<- [SYN] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], ctrl.loc_port,
              rx.meta.ipv4_hdr.src_ip[3], rx.meta.ipv4_hdr.src_ip[2],  rx.meta.ipv4_hdr.src_ip[1], rx.meta.ipv4_hdr.src_ip[0],
              rx.meta.tcp_hdr.src_port,   rx.meta.tcp_hdr.tcp_seq_num, rx.meta.tcp_hdr.tcp_ack_num
            );
            // create TCB for incoming connection
            tcb.mac_addr  <= rx.meta.mac_hdr.src_mac;
            tcb.ipv4_addr <= rx.meta.ipv4_hdr.src_ip;
            tcb.rem_port  <= rx.meta.tcp_hdr.src_port;
            tcb.loc_port  <= ctrl.loc_port;
            tcb.loc_seq   <= seq_num_prng;
            tcb.loc_ack   <= rx.meta.tcp_hdr.tcp_seq_num + 1; // Set local ack as remote seq + 1
            tcb.rem_seq   <= rx.meta.tcp_hdr.tcp_seq_num;
            tcb.rem_ack   <= rx.meta.tcp_hdr.tcp_ack_num;
            scl_raw       <= (rx.meta.tcp_opt_hdr.tcp_opt_win.win_pres) ? rx.meta.tcp_opt_hdr.tcp_opt_win.win : 1; // raw scaling option
            fsm <= con_send_syn_ack_s;
          end
        end
        con_send_syn_ack_s : begin
          if (VERBOSE) if (tx.done) $display("%d.%d.%d.%d:%d-> [SYN, ACK] to %d.%d.%d.%d:%d Seq=%h Ack=%h",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
            tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
            tcb.loc_seq, tcb.loc_ack
          );
          tx.meta.mac_known <= 1;
          tx.meta.mac_hdr.dst_mac <= tcb.mac_addr;
          // tcp header
          tx.meta.tcp_hdr.tcp_offset               <= 7;
          tx.meta.tcp_hdr.src_port                 <= tcb.loc_port;
          tx.meta.tcp_hdr.dst_port                 <= tcb.rem_port;
          tx.meta.tcp_hdr.tcp_flags                <= TCP_FLAG_SYN ^ TCP_FLAG_ACK;
          tx.meta.tcp_hdr.tcp_win_size             <= DEFAULT_WINDOW_SIZE;
          tx.meta.tcp_hdr.tcp_cks                  <= 0;
          tx.meta.tcp_hdr.tcp_pointer              <= 0;
          tx.meta.tcp_hdr.tcp_seq_num              <= tcb.loc_seq;
          tx.meta.tcp_hdr.tcp_ack_num              <= tcb.loc_ack;
          tx.meta.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
          tx.meta.tcp_opt_hdr.tcp_opt_win.win      <= 8;
          tx.meta.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
          tx.meta.tcp_opt_hdr.tcp_opt_mss.mss      <= MTU - 40;
          // ipv4 header
          tx.meta.ipv4_hdr.dst_ip <= tcb.ipv4_addr;
          tx.meta.ipv4_hdr.id     <= rx.meta.ipv4_hdr.id + 1;
          tx.meta.ipv4_hdr.length <= 20 + 28;
          tx.rdy <= 1;
          fsm <= con_syn_ack_sent_s;
        end
        con_syn_ack_sent_s : begin
          if (tx.ack) tx.rdy <= 0;
          if (ack_rec) begin
            if (VERBOSE) $display("%d.%d.%d.%d:%d<- [ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h. Connection established",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
		          rx.meta.ipv4_hdr.src_ip[3],rx.meta.ipv4_hdr.src_ip[2],rx.meta.ipv4_hdr.src_ip[1], rx.meta.ipv4_hdr.src_ip[0], rx.meta.tcp_hdr.src_port,
              rx.meta.tcp_hdr.tcp_seq_num, rx.meta.tcp_hdr.tcp_ack_num);
            fsm <= scl_s;
            tcb.loc_seq <= tcb.loc_seq + 1;
            tcb.rem_ack <= rx.meta.tcp_hdr.tcp_ack_num;
            tcb.rem_seq <= rx.meta.tcp_hdr.tcp_seq_num;
          end
        end
        /////////////////////
        // Pre-established //
        /////////////////////
        scl_s : begin // compute actual scaling option for multiplication by shifting it
          scl_ctr <= scl_ctr + 1;
          tcb.scl <= tcb.scl << 1;
          if (scl_ctr == scl_raw) fsm <= init_s;
        end
        init_s : begin
          tmr_en_con <= 0;
          tx.rdy <= 0;
          $display("%d.%d.%d.%d:%d: TCP initializing Seq=%h, Ack=%h",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
            tcb.loc_seq, tcb.loc_ack);
          tx_ctrl.init <= 1;
          rx_ctrl.init <= 1;
          fsm <= established_idle_s;
        end
        /////////////////
        // Established //
        /////////////////
        established_idle_s : begin
          sent <= 0;
          ctrl.connected                           <= 1;
          tx_ctrl.init                             <= 0;
          rx_ctrl.init                             <= 0;
          tx_ctrl.sent                             <= 0;
          rx_ctrl.ack_sent                         <= 0;
          keepalive_sent                           <= 0;
          tx.meta.tcp_hdr.src_port                 <= tcb.loc_port;
          tx.meta.tcp_hdr.dst_port                 <= tcb.rem_port;
          tx.meta.tcp_hdr.tcp_ack_num              <= rx_ctrl.loc_ack;
          tx.meta.tcp_hdr.tcp_offset               <= 5;
          tx.meta.tcp_hdr.tcp_win_size             <= DEFAULT_WINDOW_SIZE;
          tx.meta.tcp_hdr.tcp_cks                  <= 0;
          tx.meta.tcp_hdr.tcp_pointer              <= 0;
          tx.meta.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 0;
          tx.meta.tcp_opt_hdr.tcp_opt_win.win_pres <= 0;
//          tcb.loc_ack <= rx_ctrl.loc_ack; // loc_ack in tcb is updated from rx_ctrl after sending a packet with that ack.
          tcb.loc_seq <= tx_ctrl.loc_seq; // loc_seq in tcb is constantly updated from tx control
          if (port_flt) begin // update remote seq/ack
            tcb.win_scl <= rx.meta.tcp_hdr.tcp_win_size * tcb.scl;
            tcb.rem_ack <= rx.meta.tcp_hdr.tcp_ack_num; // copy ack number 
            tcb.rem_seq <= rx.meta.tcp_hdr.tcp_seq_num + rx.meta.pld_len; // true remote sequence of other host is with added pld length
          end
          // reset ready flag when tx is done
          // Payload transmission
          // If 
          if (tx_ctrl.send) begin
            if (VERBOSE) if (!tx.rdy) $display("%d.%d.%d.%d:%d-> [PSH ,ACK] to %d.%d.%d.%d:%d Seq=%h Ack=%h Len=%h.",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              tx_ctrl.pkt_seq, tcb.loc_ack, tx_ctrl.len);   
            tx_type <= tx_payload;
            tx.rdy <= 1;
            tx.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_PSH ^ TCP_FLAG_ACK;
            tx.meta.tcp_hdr.tcp_seq_num <= tx_ctrl.pkt_seq;
            tx.meta.pld_len             <= tx_ctrl.len;
            tx.meta.pld_cks             <= tx_ctrl.cks;
            tx.meta.ipv4_hdr.length     <= tx_ctrl.len + 40;
          end
          else if (send_keepalive) begin
            if (VERBOSE) if (!tx.rdy) $display("%d.%d.%d.%d:%d-> [ACK] Keep-alive to %d.%d.%d.%d:%d Seq=%h Ack=%h",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              tcb.loc_seq - 1, tcb.loc_ack);
            tx_type <= tx_keepalive;
            tx.rdy <= 1;
            tx.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_ACK;
            tx.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq - 1;
            tx.meta.pld_len             <= 0;
            tx.meta.pld_cks             <= 0;
            tx.meta.ipv4_hdr.length     <= 40;
          end
          else if (rx_ctrl.send_ack) begin
            if (VERBOSE) if (!tx.rdy) $display("%d.%d.%d.%d:%d-> [ACK] Force Ack to %d.%d.%d.%d:%d Seq=%h Ack=%h.",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              tcb.loc_seq, tcb.loc_ack);
            tx_type <= tx_forced_ack;
            tx.rdy <= 1;
            tx.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_ACK;
            tx.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq;
            tx.meta.pld_len             <= 0;
            tx.meta.pld_cks             <= 0;
            tx.meta.ipv4_hdr.length     <= 40;
          end
          if (tx_type != tx_idle) fsm <= established_tx_s;
          else if (close != close_none) fsm <= flush_s;
          // user-intiated disconnect or retransmissions failed for RETRANSMISSION_TRIES will close connection via active-close route
          if (keepalive_dcn || tx_ctrl.force_dcn || ((con_type == tcp_client) && !ctrl.connect) || ((con_type == tcp_server) && !ctrl.listen)) close <= close_active;
          // if remote side wishes to close connection, go with passive close
          else if (port_flt && rx.meta.tcp_hdr.tcp_flags.fin) close <= close_passive;
  		    // if rst flag recevied, skip connection termination
          else if (port_flt && rx.meta.tcp_hdr.tcp_flags.rst) close <= close_reset;
        end
        established_tx_s : begin
          tcb.loc_seq <= tx_ctrl.loc_seq; // loc_seq in tcb is constantly updated from tx control
          tcb.loc_ack <= rx_ctrl.loc_ack; // loc_ack in tcb is updated from rx_ctrl after sending a packet with that ack.
          if (port_flt) begin // update remote seq/ack
            tcb.win_scl <= rx.meta.tcp_hdr.tcp_win_size * tcb.scl;
            tcb.rem_ack <= rx.meta.tcp_hdr.tcp_ack_num; // copy ack number 
            tcb.rem_seq <= rx.meta.tcp_hdr.tcp_seq_num + rx.meta.pld_len; // true remote sequence of other host is with added pld length
          end
          if (tx.ack) tx.rdy <= 0;
          if (tx.done) begin
            case (tx_type)
              tx_payload    : tx_ctrl.sent     <= 1;
              tx_keepalive  : keepalive_sent   <= 1;
              tx_forced_ack : rx_ctrl.ack_sent <= 1;
            endcase
            sent <= 1;
            tx_type <= tx_idle;
          end 
          if (sent) fsm <= established_idle_s;
        end
        flush_s : begin
          tcb.loc_seq <= tcb.rem_ack; // force local seq to remote ack, discard unacked data
          tx_ctrl.flush <= 1;
          // either way, memory in tx tx_ctrl should be flushed because RAM contents can't be simply reset
  		    // it is necessary to flush it for future connections
          // wait till tx_ctrl is flushed...
          if (tx_ctrl.flushed) begin
            case (close)
              close_active  : fsm <= dcn_send_fin_s;
              close_passive : fsm <= dcn_send_ack_s;
              close_reset   : fsm <= dcn_send_rst_s;
            endcase
          end
        end
        ////////////////////////
        // Connection closure //
        ////////////////////////
        dcn_send_fin_s : begin
          tmr_en_dcn <= 1;
          tx.rdy     <= 1;
          tx.meta.ipv4_hdr.dst_ip     <= tcb.ipv4_addr;
          tx.meta.ipv4_hdr.length     <= 40;
          tx.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_ACK ^ TCP_FLAG_FIN;
          tx.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq; // Close connection at remote Ack
          tx.meta.tcp_hdr.tcp_ack_num <= tcb.loc_ack;
          tx.meta.pld_len             <= 0;
          tx.meta.pld_cks             <= 0;
          if (tx.ack) fsm <= dcn_fin_sent_s;
        end
        dcn_fin_sent_s : begin // fin_wait_1 and fin_wait_2;
          tx.rdy <= 0;
          if (port_flt && rx.meta.tcp_hdr.tcp_flags.ack) last_ack_rec <= 1; // go to fin_wait_2
          if (last_ack_rec) begin
            if (close == close_passive) fin_rst <= 1;
            if (port_flt && rx.meta.tcp_hdr.tcp_flags.fin) fsm <= dcn_send_ack_s;       
          end
        end
        dcn_send_ack_s : begin
          tmr_en_dcn <= 1;
          tx.rdy     <= 1;
          tx.meta.ipv4_hdr.dst_ip     <= tcb.ipv4_addr;
          tx.meta.ipv4_hdr.length     <= 40;
          tx.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_ACK;
          tx.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq;
          tx.meta.tcp_hdr.tcp_ack_num <= tcb.loc_ack + 1;
          tx.meta.pld_len             <= 0;
          tx.meta.pld_cks             <= 0;
          if (tx.ack) begin
            fsm <= dcn_ack_sent_s;
            tcb.loc_ack <= tcb.loc_ack + 1;
          end
        end
        dcn_ack_sent_s : begin
          tx.rdy <= 0;
          // check for tx.done before sending FIN after ACK
          if (tx.done && close == close_passive) fsm <= dcn_send_fin_s;
          if (port_flt && rx.meta.tcp_hdr.tcp_flags.ack) fin_rst <= 1;
        end
        dcn_send_rst_s : begin
          tmr_en_dcn <= 1;
          tx.rdy     <= 1;
          tx.meta.ipv4_hdr.dst_ip     <= tcb.ipv4_addr;
          tx.meta.ipv4_hdr.length     <= 40;
          tx.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_RST ^ TCP_FLAG_ACK;
          tx.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq;
          tx.meta.tcp_hdr.tcp_ack_num <= tcb.loc_ack;
          tx.meta.pld_len             <= 0;
          tx.meta.pld_cks             <= 0;
          if (tx.done) fin_rst <= 1;
        end     
      endcase
      // Constants
      tx.meta.ipv4_hdr.src_ip <= dev.ipv4_addr;
      tx.meta.ipv4_hdr.qos    <= 0;
      tx.meta.ipv4_hdr.ver    <= 4;
      tx.meta.ipv4_hdr.proto  <= TCP; // 6
      tx.meta.ipv4_hdr.df     <= 1;
      tx.meta.ipv4_hdr.mf     <= 0;
      tx.meta.ipv4_hdr.ihl    <= 5;
      tx.meta.ipv4_hdr.ttl    <= 64; // default TTL
      tx.meta.ipv4_hdr.fo     <= 0;
      tx.meta.ipv4_hdr.zero   <= 0;
    end
  end

  ////////////////////
  // TCP Keep-Alive //
  ////////////////////

  tcp_vlg_keepalive #(
    .PERIOD   (KEEPALIVE_PERIOD),
    .INTERVAL (KEEPALIVE_INTERVAL),
    .ENABLE   (ENABLE_KEEPALIVE),
    .TRIES    (KEEPALIVE_TRIES),
    .VERBOSE  (VERBOSE))
  tcp_vlg_keepalive_inst (
    .clk    (clk),
    .rst    (tcp_rst),
    .tcb    (tcb),
    .rx     (rx),
    .send   (send_keepalive), // Send send event
    .sent   (keepalive_sent),
    .dcn    (keepalive_dcn),  // Force disconnect (due to send timeout)
    .con    (ctrl.connected)  // TCP is connected
  );

endmodule : tcp_vlg_engine
