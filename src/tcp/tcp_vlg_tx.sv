module tcp_vlg_tx
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int RAM_DEPTH = 10
)(
  input logic      clk,
  input logic      rst,
  tcp.in_tx        tcp,
  ipv4.out_tx      ipv4
);
  localparam MIN_TCP_HDR_LEN = 20;
  localparam MAX_TCP_HDR_LEN = 60;
  localparam HDR_OPTIONS_POS = 13;
  
  tcp_hdr_t tcp_hdr;
  
  logic fsm_rst;
  logic [0:MAX_TCP_HDR_LEN-1][7:0] hdr, hdr_calc;
  
  logic [31:0] pseudo_hdr_cks, hdr_cks;
  
  logic calc_done;
  logic [0:39][7:0] opt_hdr;
  logic [0:11][7:0] pseudo_hdr;
  
  logic [31:0] cks_carry;
  logic [15:0] calc_cnt;
  logic [15:0] cks;
   
  logic [16:0] cks_summ; // extra bit for sum's carry
  logic [15:0] pseudo_hdr_pkt_len;
 
  logic [7:0] tcp_sack_len;
  tcp_opt_type_t opt;
  
  logic [0:14][31:0] opt_hdr_proto;
  logic [0:14]       opt_hdr_pres;
  logic [$clog2(MAX_TCP_HDR_LEN+1)-1:0] hdr_cnt;

  logic [3:0] opt_cnt;

  assign cks_summ[16:0] = cks_carry[31:16] + cks_carry[15:0]; // Calculate actual cks
  assign cks = ~(cks_summ[15:0] + cks_summ[16]);
  
  enum logic [7:0] {
    idle_s,
    opt_shift_s,
    hdr_concat_s,
    checksum_s,
    rdy_s,
    hdr_s,
    pld_s,
    wait_s
  } fsm;

  length_t hdr_len, pld_len, pld_cnt;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      pld_cnt            <= 0;
      fsm                <= idle_s;
      hdr                <= 0;
      hdr_cks            <= 0;
      pseudo_hdr_cks     <= 0;
      cks_carry          <= 0;
      calc_done          <= 0;
      calc_cnt           <= 0;
      pseudo_hdr         <= 0;
      hdr_len            <= 0;
      pld_len            <= 0;
      tcp.req            <= 0;
      tcp.acc            <= 0;
      ipv4.rdy           <= 0;
      ipv4.strm          <= 0;
      pseudo_hdr_pkt_len <= 0;
      opt_cnt            <= 0;
      opt_hdr_proto      <= 0;
      opt_hdr_pres       <= 0;
      hdr_cnt            <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (tcp.rdy) begin
            tcp.acc <= 1;
            fsm <= (tcp.meta.tcp_hdr.tcp_offset == 5) ? hdr_concat_s : opt_shift_s; // Save time if there are no options
            tcp_hdr <= tcp.meta.tcp_hdr;
            hdr_len <= tcp.meta.tcp_hdr.tcp_offset << 2; // Calculate header length in bytes
           // ipv4.meta.ipv4_hdr        <= tcp.meta.ipv4_hdr;
            ipv4.meta.ipv4_hdr.ver         <= 4;
            ipv4.meta.ipv4_hdr.ihl         <= 5;
            ipv4.meta.ipv4_hdr.qos         <= 0;
            //ipv4.meta.ipv4_hdr.length      <= 0;
            ipv4.meta.ipv4_hdr.id          <= tcp.meta.ip_pkt_id;
            ipv4.meta.ipv4_hdr.zero        <= 0;
            ipv4.meta.ipv4_hdr.df          <= 1;
            ipv4.meta.ipv4_hdr.mf          <= 0;
            ipv4.meta.ipv4_hdr.fo          <= 0;
            ipv4.meta.ipv4_hdr.ttl         <= 64; // default TTL
            ipv4.meta.ipv4_hdr.proto       <= TCP;
            ipv4.meta.ipv4_hdr.cks         <= 0;
            ipv4.meta.ipv4_hdr.src_ip      <= tcp.meta.src_ip;
            ipv4.meta.ipv4_hdr.dst_ip      <= tcp.meta.dst_ip;
            //ipv4.meta.ipv4_hdr.length       <= (tcp.meta.tcp_hdr.tcp_offset << 2) + tcp.meta.pld_len;
            ipv4.meta.mac_hdr   <= tcp.meta.mac_hdr;
            ipv4.meta.pld_len   <= (tcp.meta.tcp_hdr.tcp_offset << 2) + tcp.meta.pld_len;
            ipv4.meta.mac_known <= tcp.meta.mac_known;
            pld_len             <= tcp.meta.pld_len;
            cks_carry           <= tcp.meta.pld_cks; // initialize cks with payload checksum
            opt_hdr_proto <= {
              tcp.meta.tcp_opt.tcp_opt_timestamp.snd,
              tcp.meta.tcp_opt.tcp_opt_timestamp.rec,
              {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_TIMESTAMP, 8'd10},
              tcp.meta.tcp_opt.tcp_opt_sack.block[3].right,
              tcp.meta.tcp_opt.tcp_opt_sack.block[3].left,
              tcp.meta.tcp_opt.tcp_opt_sack.block[2].right,
              tcp.meta.tcp_opt.tcp_opt_sack.block[2].left,
              tcp.meta.tcp_opt.tcp_opt_sack.block[1].right,
              tcp.meta.tcp_opt.tcp_opt_sack.block[1].left,
              tcp.meta.tcp_opt.tcp_opt_sack.block[0].right,
              tcp.meta.tcp_opt.tcp_opt_sack.block[0].left,
              {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_SACK, tcp_sack_len},
              {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_SACK_PERM, 8'd2},
              {TCP_OPT_NOP, TCP_OPT_WIN, 8'd3, tcp.meta.tcp_opt.tcp_opt_wnd.wnd},
              {TCP_OPT_MSS, 8'd4, tcp.meta.tcp_opt.tcp_opt_mss.mss[1], tcp.meta.tcp_opt.tcp_opt_mss.mss[0]}
            }; // options prototype. Fill it with all possible options
            opt_hdr_pres <= {
              {3{tcp.meta.tcp_opt.tcp_opt_pres.timestamp_pres}},
              {2{tcp.meta.tcp_opt.tcp_opt_pres.sack_pres && tcp.meta.tcp_opt.tcp_opt_sack.block_pres[3]}},
              {2{tcp.meta.tcp_opt.tcp_opt_pres.sack_pres && tcp.meta.tcp_opt.tcp_opt_sack.block_pres[2]}},
              {2{tcp.meta.tcp_opt.tcp_opt_pres.sack_pres && tcp.meta.tcp_opt.tcp_opt_sack.block_pres[1]}},
              {2{tcp.meta.tcp_opt.tcp_opt_pres.sack_pres && tcp.meta.tcp_opt.tcp_opt_sack.block_pres[0]}},
                 tcp.meta.tcp_opt.tcp_opt_pres.sack_pres,
                 tcp.meta.tcp_opt.tcp_opt_pres.sack_perm_pres,
                 tcp.meta.tcp_opt.tcp_opt_pres.wnd_pres,
                 tcp.meta.tcp_opt.tcp_opt_pres.mss_pres
            }; // Set which option fields are present
            pseudo_hdr_pkt_len <= tcp.meta.pld_len;    
          end
        end
        opt_shift_s : begin // option assembly
          opt_cnt <= opt_cnt + 1;
          opt_hdr_proto[0:13] <= opt_hdr_proto[1:14];
          opt_hdr_pres[0:13] <= opt_hdr_pres[1:14];
          if (opt_hdr_pres[0]) begin // Shift by 32 bit chunks and attach to actual header if that option is present
            opt_hdr[0:3] <= opt_hdr_proto[0];
            opt_hdr[4:39] <= opt_hdr[0:35];
          end
          if (opt_cnt == (MAX_TCP_OFFSET - 1)) fsm <= hdr_concat_s;
        end
        hdr_concat_s : begin
          hdr_calc <= {tcp_hdr, opt_hdr};
          pseudo_hdr <= {tcp.meta.src_ip, tcp.meta.dst_ip, 8'h0, TCP, ipv4.meta.pld_len}; // assemble pseudo header
          fsm <= checksum_s;
        end
        checksum_s : begin
          calc_cnt <= calc_cnt + 1;
          pseudo_hdr[0:9] <= pseudo_hdr[2:11]; // shift tcp header and options by 16 bits
          hdr_calc[0:MAX_TCP_HDR_LEN-3] <= hdr_calc[2:MAX_TCP_HDR_LEN-1];
          pseudo_hdr_cks <= pseudo_hdr_cks + pseudo_hdr[0:1]; // Pseudo header checksum calculation
          hdr_cks <= hdr_cks + hdr_calc[0:1]; // TCP header checksum calculation
          if (calc_cnt == 6) cks_carry <= cks_carry + pseudo_hdr_cks; // Pseudo header length is 12 bytes (6 ticks by 16 bits)
          else if (calc_cnt == (hdr_len >> 1)) begin // Header has variable length, calc takes variable amount of ticks
            calc_done <= 1; 
            cks_carry <= cks_carry + hdr_cks;
          end
          if (calc_done) begin
            // Compose header to be transmitted
            hdr[0:1]     <= tcp_hdr.src_port;
            hdr[2:3]     <= tcp_hdr.dst_port;
            hdr[4:7]     <= tcp_hdr.tcp_seq_num;
            hdr[8:11]    <= tcp_hdr.tcp_ack_num;
            hdr[12][7:4] <= tcp_hdr.tcp_offset;
            {hdr[12][0], hdr[13][7:0]} <= tcp_hdr.tcp_flags;
            hdr[14:15]   <= tcp_hdr.tcp_wnd_size;
            hdr[16:17]   <= cks; // Checksum needs to be ready at byte 16
            hdr[18:19]   <= tcp_hdr.tcp_pointer;
            // Attach 
            hdr[MIN_TCP_HDR_LEN:MAX_TCP_HDR_LEN-1] <= opt_hdr;
            fsm <= rdy_s;
          end
        end
        rdy_s : begin
          if (ipv4.acc) begin
            fsm <= hdr_s;
            ipv4.rdy <= 0;
          end
          else ipv4.rdy <= 1;
        end
        hdr_s : begin // header transmission
          ipv4.rdy <= 0;
          if (ipv4.req) begin
            hdr_cnt <= hdr_cnt + 1;
            ipv4.strm.sof <= (hdr_cnt == 0);
            ipv4.strm.dat <= hdr[0];
            ipv4.strm.val <= 1;
            hdr <= hdr << ($bits(byte));
          end
          if ((hdr_cnt == hdr_len - 2) && pld_len != 0) tcp.req <= 1;
          if ((hdr_cnt == hdr_len - 1)) begin
            if (pld_len == 0) begin
              fsm <= wait_s;
              ipv4.strm.eof <= 1;
            end
            else fsm <= pld_s;
          end
        end
        pld_s : begin // pld transmission
          pld_cnt <= pld_cnt + 1;
          ipv4.strm.dat <= tcp.strm.dat;
          ipv4.strm.eof <= (pld_cnt == pld_len - 1);
          if (pld_cnt == pld_len - 1) fsm <= wait_s;
        end
        wait_s : begin
          ipv4.strm.sof <= 0;
          ipv4.strm.dat <= 0;
          ipv4.strm.val <= 0;
          ipv4.strm.eof <= 0;
          ipv4.rdy      <= 0;
        end
      endcase
    end
  end
  
  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= ipv4.done;
  always_ff @ (posedge clk) if (rst) tcp.done <= 0; else tcp.done <= ipv4.done;
  
  always_comb begin
    case (tcp.meta.tcp_opt.tcp_opt_sack.block_pres)
      4'b0000 : tcp_sack_len <= 0;
      4'b1000 : tcp_sack_len <= 10;
      4'b1100 : tcp_sack_len <= 18;
      4'b1110 : tcp_sack_len <= 26;
      4'b1111 : tcp_sack_len <= 34;
      default : tcp_sack_len <= 0;
    endcase
  end
  
endmodule : tcp_vlg_tx
  