module tcp_vlg_rx 
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
(
  input logic clk,
  input logic rst,
  ipv4.in_rx  ipv4,
  tcp.out_rx  tcp
);

  logic [15:0] byte_cnt;
  logic        fsm_rst;
  
  logic [tcp_vlg_pkg::TCP_HDR_LEN-1:0][7:0] hdr;
  
  logic receiving;
  logic hdr_done;
  
  logic [5:0] offset_bytes;
    // Latch header
  logic opt_en, rst_reg, err_len;
  tcp_opt_field_t opt_field;
  logic [7:0] opt_len;
  tcp_opt_t cur_opt;

  enum logic [4:0] {idle_s, hdr_s, opt_s, pld_s, rst_s} fsm;
  logic [$clog2(TCP_HDR_LEN+1)-1:0] hdr_byte_cnt;
  logic [5:0] opt_byte_cnt;
  length_t len, pld_byte_cnt;

  logic [5:0] opt_byte_len;

  assign fsm_rst = rst || rst_reg;

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm          <= idle_s;
      hdr_done     <= 0;
      receiving    <= 0;
      err_len      <= 0;
      byte_cnt     <= 0;
      tcp.strm     <= 0;
      tcp.meta     <= 0;
      offset_bytes <= 0;
      opt_len      <= 0;
      cur_opt      <= tcp_opt_nop;
      opt_en       <= 0;
      hdr_byte_cnt <= 0;
      opt_byte_cnt <= 0;
      pld_byte_cnt <= 0;
      opt_field    <= tcp_opt_field_kind;
      hdr          <= 0;
      rst_reg      <= 0;
      len          <= 0;
    end
    else begin
      hdr[tcp_vlg_pkg::TCP_HDR_LEN-1:1] <= hdr[tcp_vlg_pkg::TCP_HDR_LEN-2:0];
      hdr[0] <= ipv4.strm.dat;
      case (fsm)
        idle_s : begin
          if (ipv4.strm.val && ipv4.strm.sof && (ipv4.meta.ipv4_hdr.proto == TCP)) begin
            tcp.meta.mac_hdr  <= ipv4.meta.mac_hdr;
            tcp.meta.ipv4_hdr <= ipv4.meta.ipv4_hdr;
            len <= ipv4.meta.pld_len;
            fsm <= hdr_s;
          end    
        end
        hdr_s : begin
          hdr_byte_cnt <= hdr_byte_cnt + 1;
          if (hdr_byte_cnt == tcp_vlg_pkg::HDR_OPTIONS_POS-1) offset_bytes <= ipv4.strm.dat[7:4] << 2; // TCP offeset field will be exactly at [7:4]. multiply by 4
          tcp.meta.pld_len <= len - offset_bytes; // Calculate TCP payload length
          // Choose the way to proceed based on offset and layload length:
          // - if offset_bytes is more then 5, there are TCP options, proceed to options processing state opt_s
          // - if Payload length is zero length, process to reset state
          // - if Payload length is non-zero length, process to payload processing state pld_s
          if (hdr_byte_cnt == TCP_HDR_LEN - 2) begin
            fsm <= (offset_bytes == TCP_HDR_LEN) ? (tcp.meta.pld_len == 0) ? rst_s : pld_s : opt_s; 
            tcp.meta.tcp_hdr <= {hdr[18:0], ipv4.strm.dat};
          end
        end
        opt_s : begin
          opt_byte_cnt <= opt_byte_cnt + 1;
          // If there is no payload, skip it and process to reset state
          if (opt_byte_cnt == offset_bytes) fsm <= (tcp.meta.pld_len == 0) ? rst_s : pld_s;
          case (opt_field)
            tcp_opt_field_kind : begin
              case (ipv4.strm.dat)
                TCP_OPT_END : begin
                //  $display("Option kind: end");
                  opt_field <= tcp_opt_field_kind;
                  cur_opt <= tcp_opt_end;
                end
                TCP_OPT_NOP : begin
                //  $display("Option kind: NOP");
                  opt_field <= tcp_opt_field_kind;
                  cur_opt <= tcp_opt_nop;
                end
                TCP_OPT_MSS : begin
                //  $display("Option kind: MSS");
                  tcp.meta.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
                  opt_field <= tcp_opt_field_len;
                  cur_opt <= tcp_opt_mss;
                end
                TCP_OPT_WIN : begin
                //  $display("Option kind: wnd");
                  tcp.meta.tcp_opt_hdr.tcp_opt_wnd.wnd_pres <= 1;
                  opt_field <= tcp_opt_field_len;
                  cur_opt <= tcp_opt_wnd; 
                end
                TCP_OPT_SACK_PERM : begin
                //  $display("Option kind: SACK Permitted");
                  tcp.meta.tcp_opt_hdr.tcp_opt_sack_perm.sack_perm_pres <= 1;
                  opt_field <= tcp_opt_field_len;
                  cur_opt <= tcp_opt_sack_perm;
                end
                TCP_OPT_SACK : begin
                //  $display("Option kind: SACK");
                  tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack_pres <= 1;
                  opt_field <= tcp_opt_field_len;
                  cur_opt <= tcp_opt_sack;  
                end
                TCP_OPT_TIMESTAMP : begin
                //  $display("Option kind: timestamp");
                  tcp.meta.tcp_opt_hdr.tcp_opt_timestamp.timestamp_pres <= 1;
                  opt_field <= tcp_opt_field_len;
                  cur_opt <= tcp_opt_timestamp;
                end
                default : begin
                  opt_field <= tcp_opt_field_kind;
                end
              endcase
              opt_byte_len <= 0;
            end
            tcp_opt_field_len : begin
              case (ipv4.strm.dat) // Only SACK has variable length
                10      : tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 1;
                18      : tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 2;
                26      : tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 3;
                34      : tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 4;
                default : tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 0;
              endcase
              opt_len <= ipv4.strm.dat - 2; // exclude kind and length bytes
              opt_field <= (ipv4.strm.dat == 2) ? tcp_opt_field_kind : tcp_opt_field_data;
            end
            tcp_opt_field_data : begin
              opt_byte_len <= opt_byte_len + 1;
              if (opt_byte_len == opt_len - 1) begin
                opt_field <= tcp_opt_field_kind;
                case (cur_opt)
                  tcp_opt_mss : begin
                  //  $display("MSS Option value: %d", opt_data[1:0]);
                    tcp.meta.tcp_opt_hdr.tcp_opt_mss.mss <= {hdr[0], ipv4.strm.dat};
                  end
                  tcp_opt_wnd : begin
                  //  $display("Window Option value: %d", opt_data[0]);
                    tcp.meta.tcp_opt_hdr.tcp_opt_wnd.wnd <= ipv4.strm.dat;
                  end
                  tcp_opt_sack : begin
                  //  $display("SACK Option value: Begin: %h, End: %h", opt_data[7:4], opt_data[3:0]);
                  //  tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack[0].left  <= {hdr[6:3], ipv4.strm.dat};
                  //  tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack[0].right <= {hdr[2:0], ipv4.strm.dat};
                  //  tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack[3:1] <= tcp.meta.tcp_opt_hdr.tcp_opt_sack.sack[2:0];
                  end
                  tcp_opt_timestamp : begin
                    tcp.meta.tcp_opt_hdr.tcp_opt_timestamp.timestamp <= {hdr[0], ipv4.strm.dat};
                  end
                endcase
              end
            end
          endcase
        end
        pld_s : begin
          pld_byte_cnt <= pld_byte_cnt + 1;
          if (pld_byte_cnt == tcp.meta.pld_len - 1) fsm <= rst_s;
          tcp.meta.val <= 1;
          tcp.strm.dat <= ipv4.strm.dat;
          tcp.strm.sof <= pld_byte_cnt == 0;
          tcp.strm.eof <= (pld_byte_cnt == tcp.meta.pld_len - 1);
          tcp.strm.val <= 1;
        end
        rst_s : begin
          tcp.meta.val <= 1;
          tcp.strm.dat <= 0;
          tcp.strm.sof <= 0;
          tcp.strm.eof <= 0;
          tcp.strm.val <= 0;
          rst_reg      <= 1;
        end
      endcase
    end
  end
  //always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= (tcp.strm.err || tcp.strm.eof);
  

endmodule : tcp_vlg_rx
