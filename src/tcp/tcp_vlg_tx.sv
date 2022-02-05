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
  tcp_ifc.in_tx    tcp,
  ipv4_ifc.out_tx  ipv4
);
  localparam MIN_TCP_HDR_LEN = 20;
  localparam MAX_TCP_HDR_LEN = 60;
  localparam MAX_TCP_OPT_LEN = 40;

  localparam HDR_OPTIONS_POS = 13;
  
  tcp_hdr_t tcp_hdr;
  
  logic calc;
  logic fsm_rst;
    
  logic cks_done;

  logic [MAX_TCP_HDR_LEN-1:0][7:0] hdr;
  logic [MAX_TCP_OPT_LEN-1:0][7:0] opt_hdr;
  logic [11:0][7:0] pseudo_hdr;
  
  logic [15:0] calc_cnt;
  logic [15:0] cks;
   
  logic [16:0] cks_summ; // extra bit for sum's carry
 
  logic [7:0] tcp_sack_len;
  tcp_opt_type_t opt;
  
  logic [14:0][31:0] opt_hdr_proto;
  logic [14:0]       opt_hdr_pres;
  logic [$clog2(MAX_TCP_HDR_LEN+1)-1:0] hdr_cnt, hdr_len;
  length_t pld_len, pld_cnt;

  logic [3:0] opt_cnt;

  enum logic [6:0] {
    idle_s,
    opt_shift_s,
    checksum_s,
    hdr_s,
    pld_s,
    wait_s
  } fsm;

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      pld_cnt            <= 0;
      fsm                <= idle_s;
      hdr                <= 0;
      calc_cnt           <= 0;
      hdr_len            <= 0;
      pld_len            <= 0;
      ipv4.rdy           <= 0;
      opt_cnt            <= 0;
      opt_hdr_proto      <= 0;
      opt_hdr_pres       <= 0;
      hdr_cnt            <= 0;
      tcp.acc            <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (tcp.rdy) begin
            tcp.acc <= 1;
            if (tcp.meta.tcp_hdr.tcp_offset == 5) begin
              calc <= 1;
              fsm <= checksum_s;
            end
            else fsm <= opt_shift_s; // Save time if there are no options
            tcp_hdr <= tcp.meta.tcp_hdr;
            hdr_len <= tcp.meta.tcp_hdr.tcp_offset << 2; // Calculate header length in bytes
            ipv4.meta.ipv4_hdr.ver    <= 4;
            ipv4.meta.ipv4_hdr.ihl    <= 5;
            ipv4.meta.ipv4_hdr.qos    <= 0;
            ipv4.meta.ipv4_hdr.id     <= tcp.meta.ip_pkt_id;
            ipv4.meta.ipv4_hdr.zero   <= 0;
            ipv4.meta.ipv4_hdr.df     <= 1;
            ipv4.meta.ipv4_hdr.mf     <= 0;
            ipv4.meta.ipv4_hdr.fo     <= 0;
            ipv4.meta.ipv4_hdr.ttl    <= 64; // default TTL
            ipv4.meta.ipv4_hdr.proto  <= TCP;
            ipv4.meta.ipv4_hdr.cks    <= 0;
            ipv4.meta.ipv4_hdr.src_ip <= tcp.meta.src_ip;
            ipv4.meta.ipv4_hdr.dst_ip <= tcp.meta.dst_ip;
            ipv4.meta.mac_hdr   <= tcp.meta.mac_hdr;
            ipv4.meta.pld_len   <= (tcp.meta.tcp_hdr.tcp_offset << 2) + tcp.meta.pld_len;
            ipv4.meta.mac_known <= tcp.meta.mac_known;
            pld_len             <= tcp.meta.pld_len;
            opt_hdr_proto <= {
              tcp.meta.tcp_opt.tcp_opt_timestamp.snd,
              tcp.meta.tcp_opt.tcp_opt_timestamp.rec,
              {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_TIMESTAMP, 8'd10},
              tcp.meta.tcp_opt.tcp_opt_sack.block[0].right,
              tcp.meta.tcp_opt.tcp_opt_sack.block[0].left,
              tcp.meta.tcp_opt.tcp_opt_sack.block[1].right,
              tcp.meta.tcp_opt.tcp_opt_sack.block[1].left,
              tcp.meta.tcp_opt.tcp_opt_sack.block[2].right,
              tcp.meta.tcp_opt.tcp_opt_sack.block[2].left,
              tcp.meta.tcp_opt.tcp_opt_sack.block[3].right,
              tcp.meta.tcp_opt.tcp_opt_sack.block[3].left,
              {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_SACK, tcp_sack_len},
              {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_SACK_PERM, 8'd2},
              {TCP_OPT_NOP, TCP_OPT_WIN, 8'd3, tcp.meta.tcp_opt.tcp_opt_wnd.wnd},
              {TCP_OPT_MSS, 8'd4, tcp.meta.tcp_opt.tcp_opt_mss.mss[1], tcp.meta.tcp_opt.tcp_opt_mss.mss[0]}
            }; // options prototype. Fill it with all possible options
            opt_hdr_pres <= {
              {3{tcp.meta.tcp_opt.tcp_opt_pres.timestamp_pres}},
              {2{tcp.meta.tcp_opt.tcp_opt_pres.sack_pres && tcp.meta.tcp_opt.tcp_opt_sack.block_pres[0]}},
              {2{tcp.meta.tcp_opt.tcp_opt_pres.sack_pres && tcp.meta.tcp_opt.tcp_opt_sack.block_pres[1]}},
              {2{tcp.meta.tcp_opt.tcp_opt_pres.sack_pres && tcp.meta.tcp_opt.tcp_opt_sack.block_pres[2]}},
              {2{tcp.meta.tcp_opt.tcp_opt_pres.sack_pres && tcp.meta.tcp_opt.tcp_opt_sack.block_pres[3]}},
                 tcp.meta.tcp_opt.tcp_opt_pres.sack_pres,
                 tcp.meta.tcp_opt.tcp_opt_pres.sack_perm_pres,
                 tcp.meta.tcp_opt.tcp_opt_pres.wnd_pres,
                 tcp.meta.tcp_opt.tcp_opt_pres.mss_pres
            }; // Set which option fields are present
          end
        end
        opt_shift_s : begin // option assembly
          opt_cnt <= opt_cnt + 1;
          opt_hdr_proto[14:1] <= opt_hdr_proto[13:0];
          opt_hdr_pres[14:1]  <= opt_hdr_pres[13:0];
          if (opt_hdr_pres[14]) begin // Shift by 32 bit chunks and attach to actual header if that option is present
            opt_hdr[MAX_TCP_OPT_LEN-1-:4] <= opt_hdr_proto[14];
            opt_hdr[MAX_TCP_OPT_LEN-5:0] <= opt_hdr[MAX_TCP_OPT_LEN-1:4];
          end
          if (opt_cnt == (MAX_TCP_OFFSET - 1)) begin
            fsm <= checksum_s;
            calc <= 1;
          end
        end
        checksum_s : begin
          calc <= 0;
          if (ipv4.req) begin
            fsm <= hdr_s;
            ipv4.rdy <= 0;
          end
          else if (cks_done) begin
            // Compose header to be transmitted
            hdr[MAX_TCP_HDR_LEN-1-:2]     <= tcp_hdr.src_port;
            hdr[MAX_TCP_HDR_LEN-3-:2]     <= tcp_hdr.dst_port;
            hdr[MAX_TCP_HDR_LEN-5-:4]     <= tcp_hdr.tcp_seq_num;
            hdr[MAX_TCP_HDR_LEN-9-:4]     <= tcp_hdr.tcp_ack_num;
            hdr[MAX_TCP_HDR_LEN-13][7:4]  <= tcp_hdr.tcp_offset;
            {hdr[MAX_TCP_HDR_LEN-13][0],
            hdr[MAX_TCP_HDR_LEN-14][7:0]} <= tcp_hdr.tcp_flags;
            hdr[MAX_TCP_HDR_LEN-15-:2]    <= tcp_hdr.tcp_wnd_size;
            hdr[MAX_TCP_HDR_LEN-17-:2]    <= cks; // Checksum needs to be ready at byte 16
            hdr[MAX_TCP_HDR_LEN-19-:2]    <= tcp_hdr.tcp_pointer;
            // Attach options
            hdr[MAX_TCP_OPT_LEN-1:0] <= opt_hdr;
            ipv4.rdy <= 1;
          end
        end
        hdr_s : begin // header transmission
          ipv4.rdy <= 0;
          hdr_cnt <= hdr_cnt + 1;
          hdr <= hdr << ($bits(byte));
          if ((hdr_cnt == hdr_len - 1)) fsm <= (pld_len == 0) ? wait_s : pld_s;
        end
        pld_s : begin // pld transmission
          pld_cnt <= pld_cnt + 1;
          if (pld_cnt == pld_len - 1) fsm <= wait_s;
        end
        wait_s :;
        default :;
      endcase
    end
  end
            

  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= eof || ipv4.err;
  
  assign pseudo_hdr = {tcp.meta.src_ip, tcp.meta.dst_ip, 8'h0, TCP, ipv4.meta.pld_len};

  always_ff @ (posedge clk) if (rst) tcp.done <= 0; else tcp.done <= ipv4.strm.eof;
  
  logic hdr_done;
  always_ff @ (posedge clk) 
    if (fsm_rst) hdr_done <= 0;
    else if (hdr_cnt == hdr_len - 1) hdr_done <= 1; // Done transmitting header, switch to buffer output

  always_ff @ (posedge clk) 
    if (fsm_rst) tcp.req <= 0;
    else if (hdr_cnt == hdr_len - 2) tcp.req <= (pld_len != 0); // Done with header, requesting data
  
  logic sof, eof, val;

  always_comb begin
    ipv4.strm.dat = (hdr_done) ? tcp.strm.dat : hdr[MAX_TCP_HDR_LEN-1];
    ipv4.strm.val = val;
    ipv4.strm.sof = sof;
    ipv4.strm.eof = val && eof;
  end

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      val <= 0;
      sof <= 0;
      eof <= 0;
    end
    else begin
      if (ipv4.req) val <= 1; else if (eof) val <= 0;
      sof <= !val && ipv4.req;
      eof <= cks_done && ((pld_len == 0) ? (hdr_cnt == hdr_len) : (pld_cnt == pld_len));
    end
  end

  always_comb begin
    case (tcp.meta.tcp_opt.tcp_opt_sack.block_pres)
      4'b0000 : tcp_sack_len = 0;
      4'b1000 : tcp_sack_len = 10;
      4'b1100 : tcp_sack_len = 18;
      4'b1110 : tcp_sack_len = 26;
      4'b1111 : tcp_sack_len = 34;
      default : tcp_sack_len = 0;
    endcase
  end

  localparam int PSEUDO_HDR_LEN = $bits(pseudo_hdr)/$bits(byte);
  // pseudo header used
  eth_vlg_checksum #(
    .BYTES_POW    (1),
    .LENGTH_BYTES (PSEUDO_HDR_LEN + TCP_HDR_LEN + MAX_TCP_OPT_LEN)
  ) checksum_inst (
    .clk  (clk),
    .rst  (fsm_rst),
    .data ({pseudo_hdr, tcp_hdr, opt_hdr}),
    .calc (calc),
    .len  (PSEUDO_HDR_LEN + hdr_len),
    .init (tcp.meta.pld_cks),
    .cks  (cks),    
    .done (cks_done)
  );

endmodule : tcp_vlg_tx
  
