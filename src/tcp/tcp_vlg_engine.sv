import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_engine #(
  parameter int    MTU                      = 1500,
  parameter int    CONNECTION_TIMEOUT       = 10000000,
  parameter int    ACK_TIMEOUT              = 125000,
  parameter int    KEEPALIVE_PERIOD         = 600000000,
  parameter int    KEEPALIVE_INTERVAL       = 125000000,
  parameter bit    ENABLE_KEEPALIVE         = 1,
  parameter int    KEEPALIVE_TRIES          = 5,
  parameter int    DEFAULT_WINDOW_SIZE      = 1000,
  parameter bit    VERBOSE                  = 0,
  parameter string DUT_STRING               = ""
)
(
  input logic  clk,
  input logic  rst,
  input dev_t  dev,

  tcp.in_rx    rx,
  tcp.out_tx   tx,

  tx_ctl.out tx_ctl,
  rx_ctl.out rx_ctl,
  tcp_ctl.in ctl
);

  tcp tx_eng (.*); // tx intrerface generated from engine (current module). To be muxed with other sources

  // Locally defined types
  // Connection type
  enum logic {
    tcp_client,
    tcp_server
  } con_type;

  // Connection closure type
  enum logic [3:0] {
    close_none,
    close_active,
    close_passive,
    close_reset
  } close;
  
  enum logic [16:0] {
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
    established_s,
    flush_s,
    dcn_send_fin_s,
    dcn_fin_sent_s,
    dcn_send_ack_s,
    dcn_ack_sent_s,
    dcn_send_rst_s
  } fsm;

  tcb_t tcb;

  logic send_ka, ka_sent, ka_dcn;
  logic last_ack_sent, last_ack_rec, tcp_rst, fin_rst;

  ipv4_vlg_pkg::id_t ipv4_id_prng;
  tcp_num_t seq_num_prng;

  logic tmr_con, tmr_rst_con, tmr_en_con, tmr_dcn, tmr_rst_dcn, tmr_en_dcn;
  tcp_scl_t scl_raw, scl_ctr; // raw window scale (max is 14)

  // Pass TCB and status to rx and tx control
  assign rx_ctl.tcb = tcb;
  assign tx_ctl.tcb = tcb;
  assign tx_ctl.status = ctl.status;
  assign rx_ctl.status = ctl.status;

  // The only source that generates payload is tx control. Pass the payload reqest signal to it
  assign tx_ctl.req = tx.req;

  //////////////////////////////
  // Random number generators //
  //////////////////////////////
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

  /////////////////////////////////////
  // Connect and disconnect timeouts //
  /////////////////////////////////////
  eth_vlg_tmr #(
    .TICKS (CONNECTION_TIMEOUT),
    .AUTORESET (1))
  con_tmr_inst (  
    .clk (clk),
    .rst (tmr_rst_con),
    .en  (tmr_en_con),
    .tmr_rst (1'b0),
    .tmr (tmr_con)
  );

  eth_vlg_tmr #(
    .TICKS (CONNECTION_TIMEOUT),
    .AUTORESET (1))
  dcn_tmr_inst (  
    .clk (clk),
    .rst (tmr_rst_dcn),
    .en  (tmr_en_dcn),
    .tmr_rst (1'b0),
    .tmr (tmr_dcn)
  );

  // Reset FSM if either:
  // - connection failed to establish in time
  // - disconnect sequence failed to complete in time
  // - FSM has finished disconnecting or received RST flag
  always @ (posedge clk) begin
    if (rst) tcp_rst <= 1;
    else tcp_rst <= tmr_con || tmr_dcn || fin_rst;
  end
  
  // Assignments for convinience
  assign usr_dcn      = ((con_type == tcp_client) && !ctl.connect) || ((con_type == tcp_server) && !ctl.listen);                 // User-initiated disconnect
  assign loc_port_flt = rx.meta.val && (rx.meta.tcp_hdr.dst_port == ctl.loc_port);                                               // Received packet's remote port matches local port in user control. used in 3WHS
  assign port_flt     = rx.meta.val && (rx.meta.tcp_hdr.src_port == tcb.rem_port) && (rx.meta.tcp_hdr.dst_port == tcb.loc_port); // Received packet's ports match current connection
  assign syn_rec      = loc_port_flt && rx.meta.tcp_hdr.tcp_flags == TCP_FLAG_SYN;                                               // SYN received for open local port
  assign syn_ack_rec  = loc_port_flt && rx.meta.tcp_hdr.tcp_flags.syn && rx.meta.tcp_hdr.tcp_flags.ack;                          // SYN ACK received for open local port
  assign ack_rec      =     port_flt && rx.meta.tcp_hdr.tcp_flags.ack && rx.meta.tcp_hdr.tcp_seq_num == tcb.rem_seq + 1;         // ACK received for 3WHS
  assign fin_rec      =     port_flt && rx.meta.tcp_hdr.tcp_flags.fin;                                                           // FIN received for current connection
  assign rst_rec      =     port_flt && rx.meta.tcp_hdr.tcp_flags.rst;                                                           // RST received for current connection

  always @ (posedge clk) begin
    if (tcp_rst) begin
      fsm              <= closed_s;
      tcb              <= '0;
      ctl.status       <= tcp_closed;
      tx_ctl.flush     <= 0;
      tx_ctl.rst       <= 1;
      con_type         <= tcp_client;
      close            <= close_none;
      tmr_en_con       <= 0;
      tmr_rst_con      <= 1;
      tmr_en_dcn       <= 0;
      tmr_rst_dcn      <= 1;
      last_ack_rec     <= 0;
      last_ack_sent    <= 0;
      fin_rst          <= 0;
      scl_raw          <= 0;
      scl_ctr          <= 0;
      tx_eng.rdy       <= 0;
      tx_eng.meta      <= 0;
    end
    else begin
      case (fsm)
        closed_s : begin
          tx_ctl.rst      <= 0;
          ctl.status      <= tcp_closed;
          tcb.scl         <= 1;
          tcb.wnd_scl     <= '1;
          tmr_rst_con     <= 0;
          tmr_rst_dcn     <= 0;
          tmr_en_con      <= 0;
          tmr_en_dcn      <= 0;
          tx_ctl.flush    <= 0;
          tx_eng.meta.pld_len <= 0;
          tx_eng.meta.pld_cks <= 0;
          if (ctl.listen) begin
            con_type <= tcp_server; // passive open (server)
            fsm      <= listen_s;
          end
          else if (ctl.connect) begin
            con_type <= tcp_client; // active open (client)
            fsm      <= con_send_syn_s;
          end
        end
        /////////////////
        // Active Open //
        /////////////////
        con_send_syn_s : begin
          ctl.status <= tcp_connecting;
          fsm <= con_syn_sent_s;
          tmr_en_con <= 1; // Start connection timer
          if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d-> [SYN] to %d.%d.%d.%d:%d Seq=%h Ack=%h",
            dev.ipv4_addr[3],dev.ipv4_addr[2],dev.ipv4_addr[1],dev.ipv4_addr[0],ctl.loc_port,
            ctl.rem_ipv4[3],ctl.rem_ipv4[2],ctl.rem_ipv4[1],ctl.rem_ipv4[0],
            ctl.rem_port, seq_num_prng, tcb.loc_ack
          );
          // Create TCB for outcoming connection
          tcb.ipv4_addr     <= ctl.rem_ipv4;
          tcb.rem_port      <= ctl.rem_port;
          tcb.loc_port      <= ctl.loc_port;
          tcb.loc_ack       <= 0; // Set local ack to 0 before acquiring remote seq
          tcb.loc_seq       <= seq_num_prng;
          tx_eng.meta.mac_known <= 0;
          // Set options at connection establishment
          tx_eng.meta.tcp_opt_hdr.tcp_opt_wnd.wnd_pres <= 1;
          tx_eng.meta.tcp_opt_hdr.tcp_opt_wnd.wnd      <= 8;
          tx_eng.meta.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
          tx_eng.meta.tcp_opt_hdr.tcp_opt_mss.mss      <= MTU - 40;
          // Set relevant IP header fields
          tx_eng.meta.ipv4_hdr.dst_ip <= ctl.rem_ipv4;
          tx_eng.meta.ipv4_hdr.id     <= ipv4_id_prng;
          tx_eng.meta.ipv4_hdr.length <= 20 + 28;
          // Set tcp header for SYN packet with options
          tx_eng.meta.tcp_hdr.tcp_offset   <= 7;
          tx_eng.meta.tcp_hdr.src_port     <= ctl.loc_port;
          tx_eng.meta.tcp_hdr.dst_port     <= ctl.rem_port;
          tx_eng.meta.tcp_hdr.tcp_flags    <= TCP_FLAG_SYN;
          tx_eng.meta.tcp_hdr.tcp_wnd_size <= DEFAULT_WINDOW_SIZE;
          tx_eng.meta.tcp_hdr.tcp_cks      <= 0;
          tx_eng.meta.tcp_hdr.tcp_pointer  <= 0;
          tx_eng.meta.tcp_hdr.tcp_seq_num  <= seq_num_prng;
          tx_eng.meta.tcp_hdr.tcp_ack_num  <= 0;
          tx_eng.rdy <= 1;
        end
        con_syn_sent_s : begin
          if (tx_eng.acc) tx_eng.rdy <= 0; // release rdy after confirmation from tcp_tx
          if (syn_ack_rec) begin // when syn-ack received...
            if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d<- [SYN, ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
              dev.ipv4_addr[3],dev.ipv4_addr[2],dev.ipv4_addr[1],dev.ipv4_addr[0],tcb.loc_port,
              rx.meta.ipv4_hdr.src_ip[3],rx.meta.ipv4_hdr.src_ip[2],rx.meta.ipv4_hdr.src_ip[1],rx.meta.ipv4_hdr.src_ip[0],
              rx.meta.tcp_hdr.src_port, rx.meta.tcp_hdr.tcp_seq_num, rx.meta.tcp_hdr.tcp_ack_num
            );
            // Fill in the TCB fields
            tcb.rem_seq <= rx.meta.tcp_hdr.tcp_seq_num + 1; 
            tcb.rem_ack <= rx.meta.tcp_hdr.tcp_ack_num;
            tcb.loc_seq <= tcb.loc_seq + 1;
            tcb.loc_ack <= rx.meta.tcp_hdr.tcp_seq_num + 1;
            // If scaling option present, capture it, otherwise set scale to 1 (no scale)
            scl_raw <= (rx.meta.tcp_opt_hdr.tcp_opt_wnd.wnd_pres) ? rx.meta.tcp_opt_hdr.tcp_opt_wnd.wnd : 1; // raw scaling option used to compute actual window scaling
            tcb.mac_addr <= rx.meta.mac_hdr.src_mac; // capture remote MAC address
            tcb.mac_known <= 1; // remote MAC is now known, will skip ARP logic later in IPv4 TX
            fsm <= con_send_ack_s;
          end
        end
        con_send_ack_s : begin
          if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d-> [ACK] to %d.%d.%d.%d:%d Seq=%h Ack=%h. Connection established",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
            tx_eng.meta.ipv4_hdr.dst_ip[3], tx_eng.meta.ipv4_hdr.dst_ip[2], tx_eng.meta.ipv4_hdr.dst_ip[1], tx_eng.meta.ipv4_hdr.dst_ip[0],
            tcb.rem_port, tcb.loc_seq, tcb.loc_ack
          );
          tx_eng.meta.tcp_opt_hdr         <= 0;
          tx_eng.meta.ipv4_hdr.id         <= tx_eng.meta.ipv4_hdr.id + 1;
          tx_eng.meta.ipv4_hdr.length     <= 20 + 20; // no payload, no options
          tx_eng.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_ACK; // ACK
          tx_eng.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq;
          tx_eng.meta.tcp_hdr.tcp_ack_num <= tcb.loc_ack;
          tx_eng.meta.tcp_hdr.tcp_offset  <= 5;
          tx_eng.meta.mac_hdr.dst_mac     <= tcb.mac_addr;
          tx_eng.rdy                      <= 1;
          fsm                             <= con_ack_sent_s;
        end
        con_ack_sent_s : begin
          if (tx_eng.acc) tx_eng.rdy <= 0;
          if (tx_eng.done) fsm <= scl_s;
        end
        //////////////////
        // Passive Open //
        //////////////////
        listen_s : begin
         ctl.status <= tcp_listening;
          if (syn_rec) begin // connection request
            if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d<- [SYN] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], ctl.loc_port,
              rx.meta.ipv4_hdr.src_ip[3], rx.meta.ipv4_hdr.src_ip[2],  rx.meta.ipv4_hdr.src_ip[1], rx.meta.ipv4_hdr.src_ip[0],
              rx.meta.tcp_hdr.src_port,   rx.meta.tcp_hdr.tcp_seq_num, rx.meta.tcp_hdr.tcp_ack_num
            );
            // create TCB for incoming connection
            tcb.mac_addr  <= rx.meta.mac_hdr.src_mac;
            tcb.ipv4_addr <= rx.meta.ipv4_hdr.src_ip;
            tcb.rem_port  <= rx.meta.tcp_hdr.src_port;
            tcb.loc_port  <= ctl.loc_port;
            tcb.loc_seq   <= seq_num_prng;
            tcb.loc_ack   <= rx.meta.tcp_hdr.tcp_seq_num + 1; // set local ack as remote seq + 1
            tcb.rem_seq   <= rx.meta.tcp_hdr.tcp_seq_num;
            tcb.rem_ack   <= rx.meta.tcp_hdr.tcp_ack_num;
            scl_raw       <= (rx.meta.tcp_opt_hdr.tcp_opt_wnd.wnd_pres) ? rx.meta.tcp_opt_hdr.tcp_opt_wnd.wnd : 1; // raw scaling option
            fsm <= con_send_syn_ack_s;
          end
        end
        con_send_syn_ack_s : begin
         ctl.status <= tcp_connecting;
          if (VERBOSE) if (tx_eng.done) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d-> [SYN, ACK] to %d.%d.%d.%d:%d Seq=%h Ack=%h",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
            tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
            tcb.loc_seq, tcb.loc_ack
          );
          tx_eng.meta.mac_known <= 1;
          tx_eng.meta.mac_hdr.dst_mac <= tcb.mac_addr;
          // tcp header
          tx_eng.meta.tcp_hdr.tcp_offset               <= 7;
          tx_eng.meta.tcp_hdr.src_port                 <= tcb.loc_port;
          tx_eng.meta.tcp_hdr.dst_port                 <= tcb.rem_port;
          tx_eng.meta.tcp_hdr.tcp_flags                <= TCP_FLAG_SYN ^ TCP_FLAG_ACK;
          tx_eng.meta.tcp_hdr.tcp_wnd_size             <= DEFAULT_WINDOW_SIZE;
          tx_eng.meta.tcp_hdr.tcp_cks                  <= 0;
          tx_eng.meta.tcp_hdr.tcp_pointer              <= 0;
          tx_eng.meta.tcp_hdr.tcp_seq_num              <= tcb.loc_seq;
          tx_eng.meta.tcp_hdr.tcp_ack_num              <= tcb.loc_ack;
          tx_eng.meta.tcp_opt_hdr.tcp_opt_wnd.wnd_pres <= 1;
          tx_eng.meta.tcp_opt_hdr.tcp_opt_wnd.wnd      <= 8;
          tx_eng.meta.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
          tx_eng.meta.tcp_opt_hdr.tcp_opt_mss.mss      <= MTU - 40;
          // ipv4 header
          tx_eng.meta.ipv4_hdr.dst_ip <= tcb.ipv4_addr;
          tx_eng.meta.ipv4_hdr.id     <= rx.meta.ipv4_hdr.id + 1;
          tx_eng.meta.ipv4_hdr.length <= 20 + 28;
          tx_eng.rdy <= 1;
          fsm <= con_syn_ack_sent_s;
        end
        con_syn_ack_sent_s : begin
          if (tx_eng.acc) tx_eng.rdy <= 0;
          if (ack_rec) begin
            if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d<- [ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h. Connection established",
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
          tx_eng.rdy <= 0;
          $display("[", DUT_STRING, "] %d.%d.%d.%d:%d: TCP initializing Seq=%h, Ack=%h",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
            tcb.loc_seq, tcb.loc_ack);
          tx_ctl.init <= 1;
          rx_ctl.init <= 1;
          fsm <= established_s;
          tx_eng.meta.tcp_hdr.tcp_cks     <= 0;
          tx_eng.meta.tcp_hdr.tcp_pointer <= 0;
          tx_eng.meta.tcp_opt_hdr         <= 0;
        end
        /////////////////
        // Established //
        /////////////////
        established_s : begin
          tx_ctl.init <= 0;
          rx_ctl.init <= 0;
          ctl.status <= tcp_connected;
          if (tx.done) tcb.loc_ack <= rx_ctl.loc_ack; // loc_ack is updated upon sending Ack
          tcb.loc_seq <= tx_ctl.loc_seq; // loc_seq in tcb is constantly updated from tx control
          // Receive
          if (port_flt) begin // update remote seq/ack
            tcb.wnd_scl <= rx.meta.tcp_hdr.tcp_wnd_size * tcb.scl; // recompute window scale
            tcb.rem_ack <= rx.meta.tcp_hdr.tcp_ack_num; // copy ack number to TCB
            tcb.rem_seq <= rx.meta.tcp_hdr.tcp_seq_num + rx.meta.pld_len; // true remote sequence of other host is with added pld length
          end
          if (ka_dcn || tx_ctl.force_dcn || usr_dcn) close <= close_active; // request connection closure
          else if (fin_rec) close <= close_passive;
          else if (rst_rec) close <= close_reset;
          if (close != close_none) fsm <= flush_s;
        end
        //////////////////////////
        // TX control RAM flush //
        //////////////////////////
        flush_s : begin
          ctl.status <= tcp_disconnecting;
          tcb.loc_seq <= tcb.rem_ack; // force local seq to remote ack, discard unacked data
          tx_ctl.flush <= 1;          // flush transmission RAM as memory cannot be reset
          if (tx_ctl.flushed) begin   // when flushed, transition to disconnect sequence
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
          tx_eng.rdy <= 1;
          tmr_en_dcn <= 1;
          tx_eng.meta.ipv4_hdr.length     <= 40;
          tx_eng.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_ACK ^ TCP_FLAG_FIN;
          tx_eng.meta.tcp_hdr.tcp_offset  <= 5;
          tx_eng.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq; // Close connection at remote Ack
          tx_eng.meta.tcp_hdr.tcp_ack_num <= tcb.loc_ack;
          tx_eng.meta.pld_len             <= 0;
          tx_eng.meta.pld_cks             <= 0;
          if (tx_eng.acc) fsm <= dcn_fin_sent_s;
        end
        dcn_fin_sent_s : begin // fin_wait_1 and fin_wait_2;
          tx_eng.rdy <= 0;
          if (port_flt && rx.meta.tcp_hdr.tcp_flags.ack) last_ack_rec <= 1; // go to fin_wait_2
          if (last_ack_rec) begin
            if (close == close_passive) fin_rst <= 1;
            if (port_flt && rx.meta.tcp_hdr.tcp_flags.fin) fsm <= dcn_send_ack_s;       
          end
        end
        dcn_send_ack_s : begin
          tx_eng.rdy <= 1;
          tmr_en_dcn <= 1;
          tx_eng.meta.ipv4_hdr.length     <= 40;
          tx_eng.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_ACK;
          tx_eng.meta.tcp_hdr.tcp_offset  <= 5;
          tx_eng.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq;
          tx_eng.meta.tcp_hdr.tcp_ack_num <= tcb.loc_ack + 1;
          tx_eng.meta.pld_len             <= 0;
          tx_eng.meta.pld_cks             <= 0;
          if (tx_eng.acc) begin
            fsm <= dcn_ack_sent_s;
            tcb.loc_ack <= tcb.loc_ack + 1;
          end
        end
        dcn_ack_sent_s : begin
          tx_eng.rdy <= 0;
          // check for tx_eng.done before sending FIN after ACK
          if (tx_eng.done && close == close_passive) fsm <= dcn_send_fin_s;
          if (port_flt && rx.meta.tcp_hdr.tcp_flags.ack) fin_rst <= 1;
        end
        dcn_send_rst_s : begin
          tx_eng.rdy <= 1;
          tmr_en_dcn <= 1;
          tx_eng.meta.ipv4_hdr.length     <= 40;
          tx_eng.meta.tcp_hdr.tcp_flags   <= TCP_FLAG_RST ^ TCP_FLAG_ACK;
          tx_eng.meta.tcp_hdr.tcp_offset  <= 5;
          tx_eng.meta.tcp_hdr.tcp_seq_num <= tcb.loc_seq;
          tx_eng.meta.tcp_hdr.tcp_ack_num <= tcb.loc_ack;
          tx_eng.meta.pld_len             <= 0;
          tx_eng.meta.pld_cks             <= 0;
          if (tx_eng.acc) fin_rst <= 1;
        end     
      endcase
      // Constants
      tx_eng.meta.ipv4_hdr.src_ip <= dev.ipv4_addr;
      tx_eng.meta.ipv4_hdr.qos    <= 0;
      tx_eng.meta.ipv4_hdr.ver    <= 4;
      tx_eng.meta.ipv4_hdr.proto  <= TCP; // 6
      tx_eng.meta.ipv4_hdr.df     <= 1;
      tx_eng.meta.ipv4_hdr.mf     <= 0;
      tx_eng.meta.ipv4_hdr.ihl    <= 5;
      tx_eng.meta.ipv4_hdr.ttl    <= 64; // default TTL
      tx_eng.meta.ipv4_hdr.fo     <= 0;
      tx_eng.meta.ipv4_hdr.zero   <= 0;
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
    .VERBOSE  (VERBOSE)
  ) tcp_vlg_keepalive_inst (
    .clk    (clk),
    .rst    (tcp_rst),
    .tcb    (tcb),
    .rx     (rx),
    .send   (send_ka), // Send send event
    .sent   (ka_sent),
    .dcn    (ka_dcn),  // Force disconnect (due to send timeout)
    .status (ctl.status)  // TCP is connected
  );

  //////////////////////
  // Transmission mux //
  //////////////////////
  
  tcp_vlg_tx_arb #(
    .DEFAULT_WINDOW_SIZE (DEFAULT_WINDOW_SIZE)
  ) tcp_vlg_tx_arb_inst (
    .clk      (clk),
    .rst      (tcp_rst),
    .tcb      (tcb),
    .dev      (dev),
    // controls and replies
    .send_ka  (send_ka),
    .ka_sent  (ka_sent),
    .send_pld (tx_ctl.send),
    .pld_sent (tx_ctl.sent),
    .pld_info (tx_ctl.pld_info),
    .send_ack (rx_ctl.send_ack),
    .ack_sent (rx_ctl.ack_sent),
    .status   (ctl.status),
    // signals from engine
    .strm     (tx_ctl.strm),
    .tx_eng   (tx_eng),
    .tx       (tx),
    
    .loc_seq  (tcb.loc_seq),
    .loc_ack  (rx_ctl.loc_ack)
  );

endmodule : tcp_vlg_engine
