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
  output logic pld_sent,
  input  logic send_ack,
  output logic ack_sent,
  // tx flow control
  input  tcp_stat_t status,
  // signals from tcp eng
  tcp.in_tx  tx_eng,
  tcp.out_tx tx,
  input stream_t strm,
  input tcp_pld_info_t pld_info,

  // from tx_ctl
  input tcp_num_t loc_seq,  // local sequence number
  input tcp_num_t last_seq, // last sequence number reported
  input tcp_num_t loc_ack   // current local ack
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
  
  always_comb begin
    tx.strm <= strm;
    tx_eng.req <= 0;
    if (status == tcp_connected) begin
      tx.rdy      <= rdy_arb;
      tx.meta     <= meta_arb;
      tx_eng.done <= 0;
      tx_eng.acc  <= 0;
      done_arb    <= tx.done;
      acc_arb     <= tx.acc;
    end 
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
      fsm      <= idle_s;
    end
    else begin
      case (fsm)
        idle_s : begin
          pld_sent <= 0;
          ka_sent  <= 0; 
          ack_sent <= 0;
          meta_arb.tcp_hdr.tcp_offset   <= TCP_DEFAULT_OFFSET;
          meta_arb.tcp_hdr.src_port     <= tcb.loc_port;
          meta_arb.tcp_hdr.dst_port     <= tcb.rem_port;
          meta_arb.tcp_hdr.tcp_wnd_size <= DEFAULT_WINDOW_SIZE;
          meta_arb.tcp_hdr.tcp_cks      <= 0;
          meta_arb.tcp_hdr.tcp_pointer  <= 0;
          meta_arb.tcp_hdr.tcp_ack_num  <= loc_ack;
          meta_arb.tcp_opt_hdr          <= 0;
          meta_arb.ipv4_hdr.src_ip      <= dev.ipv4_addr;
          meta_arb.ipv4_hdr.qos         <= 0;
          meta_arb.ipv4_hdr.ver         <= 4;
          meta_arb.ipv4_hdr.proto       <= TCP; // 6
          meta_arb.ipv4_hdr.df          <= 1;
          meta_arb.ipv4_hdr.mf          <= 0;
          meta_arb.ipv4_hdr.ihl         <= 5;
          meta_arb.ipv4_hdr.ttl         <= 64; // default TTL
          meta_arb.ipv4_hdr.fo          <= 0;
          meta_arb.ipv4_hdr.zero        <= 0;
          meta_arb.ipv4_hdr.dst_ip      <= tcb.ipv4_addr;
          meta_arb.ipv4_hdr.id          <= meta_arb.ipv4_hdr.id + 1;
          meta_arb.mac_hdr.dst_mac      <= tcb.mac_addr;
          meta_arb.mac_hdr.src_mac      <= dev.mac_addr;
          meta_arb.mac_known            <= 1;
          if (tx_type != tx_none) fsm <= active_s;
          if (send_pld) begin
            if (VERBOSE) if (!rdy_arb) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d @%t -> [PSH ,ACK] to %d.%d.%d.%d:%d Seq=%d Ack=%d Len=%d",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port, $time(),
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              pld_info.seq, tcb.loc_ack, pld_info.lng
            );   
            tx_type <= tx_pld;
            rdy_arb <= 1;
            meta_arb.tcp_hdr.tcp_flags <= TCP_FLAG_PSH ^ TCP_FLAG_ACK;
            meta_arb.tcp_hdr.tcp_seq_num <= pld_info.seq;
            meta_arb.pld_len <= pld_info.lng;
            meta_arb.pld_cks <= pld_info.cks;
            meta_arb.ipv4_hdr.length <= pld_info.lng + 40;
            //last_seq <= pld_info.seq;
          end
          else if (send_ka) begin
            if (VERBOSE) if (!rdy_arb) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d-> [ACK] Keep-alive to %d.%d.%d.%d:%d Seq=%d Ack=%d",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port,
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              tcb.loc_seq - 1, tcb.loc_ack
            );
            tx_type <= tx_ka;
            rdy_arb <= 1;
            meta_arb.tcp_hdr.tcp_flags <= TCP_FLAG_ACK;
            meta_arb.tcp_hdr.tcp_seq_num <= last_seq - 1;
            meta_arb.pld_len <= 0;
            meta_arb.pld_cks <= 0;
            meta_arb.ipv4_hdr.length <= 40;
          end
          else if (send_ack) begin
            if (VERBOSE) if (!rdy_arb) $display("[", DUT_STRING, "] %d.%d.%d.%d:%d @%t -> [ACK] Force Ack to %d.%d.%d.%d:%d Seq=%d Ack=%d",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], tcb.loc_port, $time(),
		          tcb.ipv4_addr[3], tcb.ipv4_addr[2], tcb.ipv4_addr[1], tcb.ipv4_addr[0], tcb.rem_port,
              tcb.loc_seq, tcb.loc_ack
            );
            tx_type <= tx_ack;
            rdy_arb <= 1;
            meta_arb.tcp_hdr.tcp_flags <= TCP_FLAG_ACK;
            meta_arb.tcp_hdr.tcp_seq_num <= last_seq;
            meta_arb.pld_len <= 0;
            meta_arb.pld_cks <= 0;
            meta_arb.ipv4_hdr.length <= 40;
          end
        end
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
