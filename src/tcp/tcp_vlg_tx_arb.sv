  // Scheme:
  //       +------+
  //       |engine|=========+
  //       +------+         |       
  //========================|=================
  //   +----------+   _     |   _
  //   |keep-alive|=>| \    |  | \
  //   +----------+  |  \   +=>|0 \ 
  //      +-------+  |   \     |   |===> to tx
  //      |payload|=>|arb |===>|1 /
  //      +-------+  |   /     |_/
  //   +----------+  |  /       ^
  //   |forced ack|=>|_/   [connected]  
  //   +----------+

module tcp_vlg_tx_arb
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
 #(
  parameter int    DEFAULT_WINDOW_SIZE = 1000,
  parameter bit    VERBOSE             = 1,
  parameter string DUT_STRING          = ""
)
(
  input  logic clk,
  input  logic rst,
  input  tcb_t tcb,
  input  dev_t dev,
  // controls and replies
  input  logic send_ka,
  output logic ka_sent,
  
  input  logic send_pld,
  input tcp_pld_info_t pld_info,
  output logic pld_sent,

  input  logic send_ack,
  output logic ack_sent,
  // tx flow control
  input  tcp_stat_t status,
  // signals from tcp eng
  tcp.in_tx  tx_eng,
  tcp.out_tx tx,
  input stream_t strm,
  // from rx_ctl
  input tcp_opt_sack_t sack,
  // from tx_ctl
  input  tcp_num_t last_seq, // last sequence number reported
  input  tcp_num_t loc_ack,  // current local ack number
  output tcp_num_t last_ack  // local ack actually reported
);

  enum logic [3:0] {
    tx_none = 4'b0001,
    tx_ka   = 4'b0010,
    tx_ack  = 4'b0100,
    tx_pld  = 4'b1000
  } tx_type;

  logic rdy_arb, done_arb, acc_arb;
  tcp_meta_t meta_arb; 

  enum logic [2:0] {idle_s, active_s, sent_s} fsm;

  // tx output mux
  always_comb begin
    tx.strm <= strm;
    tx_eng.req <= 0;
    // When connected, arbiter takes control of tx
    if (status == tcp_connected) begin
      tx.rdy      <= rdy_arb;
      tx.meta     <= meta_arb;
      tx_eng.done <= 0;
      tx_eng.acc  <= 0;
      done_arb    <= tx.done;
      acc_arb     <= tx.acc;
    end
    // If not connected, engine controls tx
    else begin
      tx.rdy      <= tx_eng.rdy;
      tx.meta     <= tx_eng.meta;
      tx_eng.done <= tx.done;
      tx_eng.acc  <= tx.acc;
      done_arb    <= 0;
      acc_arb     <= 0;
    end
  end
  
  always_ff @ (posedge clk) begin
    if (rst) begin
      pld_sent <= 0;
      ka_sent  <= 0;
      ack_sent <= 0;
      tx_type  <= tx_none;
      rdy_arb  <= 0;
      meta_arb <= 0;
      last_ack <= 0;
      fsm      <= idle_s;
    end
    else begin
      case (fsm)
        idle_s : begin
          pld_sent <= 0;
          ka_sent  <= 0; 
          ack_sent <= 0;

          meta_arb.tcp_hdr.src_port     <= tcb.loc_port;
          meta_arb.tcp_hdr.dst_port     <= tcb.rem_port;
          meta_arb.tcp_hdr.tcp_wnd_size <= DEFAULT_WINDOW_SIZE;
          meta_arb.tcp_hdr.tcp_cks      <= 0;
          meta_arb.tcp_hdr.tcp_pointer  <= 0;
          meta_arb.tcp_hdr.tcp_ack_num  <= loc_ack;
          meta_arb.tcp_opt.tcp_opt_sack <= sack;
          meta_arb.tcp_opt.tcp_opt_pres.sack_pres <= (sack.block_pres != 0);
          meta_arb.src_ip <= dev.ipv4_addr;
          meta_arb.dst_ip <= tcb.ipv4_addr;

          meta_arb.mac_hdr.dst_mac      <= tcb.mac_addr;
          meta_arb.mac_hdr.src_mac      <= dev.mac_addr;
          meta_arb.mac_known            <= 1;

          last_ack                     <= loc_ack;

          case (sack.block_pres)
            4'b0000 : meta_arb.tcp_hdr.tcp_offset <= TCP_DEFAULT_OFFSET;
            4'b1000 : meta_arb.tcp_hdr.tcp_offset <= TCP_DEFAULT_OFFSET + 2 + 1;
            4'b1100 : meta_arb.tcp_hdr.tcp_offset <= TCP_DEFAULT_OFFSET + 4 + 1;
            4'b1110 : meta_arb.tcp_hdr.tcp_offset <= TCP_DEFAULT_OFFSET + 6 + 1;
            4'b1111 : meta_arb.tcp_hdr.tcp_offset <= TCP_DEFAULT_OFFSET + 8 + 1;
            default : begin
              meta_arb.tcp_hdr.tcp_offset <= TCP_DEFAULT_OFFSET;
              $error("Bad SACK blocks");
            end
          endcase
          if (tx_type != tx_none) fsm <= active_s;
          if (send_pld) begin
            if (VERBOSE) if (!rdy_arb) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d @%t -> [PSH ,ACK] to %d.%d.%d.%d:%d Seq=%d Ack=%d Len=%d",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port, $time(),
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              pld_info.start, tcb.loc_ack, pld_info.lng
            );   
            tx_type <= tx_pld;
            rdy_arb <= 1;
            meta_arb.tcp_hdr.tcp_flags <= TCP_FLAG_PSH ^ TCP_FLAG_ACK;
            meta_arb.tcp_hdr.tcp_seq_num <= pld_info.start;
            meta_arb.pld_len <= pld_info.lng;
            meta_arb.pld_cks <= pld_info.cks;
          end
          else if (send_ka) begin
            if (VERBOSE) if (!rdy_arb) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d-> [ACK] Keep-alive to %d.%d.%d.%d:%d Seq=%d Ack=%d",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              last_seq - 1, tcb.loc_ack
            );
            tx_type <= tx_ka;
            rdy_arb <= 1;
            meta_arb.tcp_hdr.tcp_flags <= TCP_FLAG_ACK;
            meta_arb.tcp_hdr.tcp_seq_num <= last_seq - 1;
            meta_arb.pld_len <= 0;
            meta_arb.pld_cks <= 0;
          end
          else if (send_ack) begin
            if (VERBOSE) if (!rdy_arb) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d @%t -> [ACK] Force Ack to %d.%d.%d.%d:%d Seq=%d Ack=%d",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port, $time(),
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              last_seq - 1, tcb.loc_ack
            );
            tx_type <= tx_ack;
            rdy_arb <= 1;
            meta_arb.tcp_hdr.tcp_flags <= TCP_FLAG_ACK;
            meta_arb.tcp_hdr.tcp_seq_num <= last_seq;
            meta_arb.pld_len <= 0;
            meta_arb.pld_cks <= 0;
          end
        end
        // active transmission state
        active_s : begin
          if (acc_arb) rdy_arb <= 0;
          if (done_arb) begin
            case (tx_type)
              tx_pld : pld_sent <= 1;
              tx_ka  : ka_sent  <= 1;
              tx_ack : ack_sent <= 1;
            endcase
            tx_type <= tx_none;
            fsm <= sent_s;
            meta_arb.ip_pkt_id <= meta_arb.ip_pkt_id + 1;
          end
        end
        sent_s : begin
          fsm <= idle_s;
          pld_sent <= 0;
          ka_sent  <= 0;
          ack_sent <= 0;
        end
      endcase
    end
  end


endmodule : tcp_vlg_tx_arb
