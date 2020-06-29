
import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_rx (
  input logic clk,
  input logic rst,
  input dev_t dev,
  ipv4.in     rx,
  tcp.out     tcp
);

localparam MIN_HDR_LEN = 20;
localparam HDR_OPTIONS_POS = 13;

logic [15:0] byte_cnt;
logic        fsm_rst;

logic [0:MIN_HDR_LEN-1][7:0] hdr;

logic receiving;
logic hdr_done;

logic tcp_err;
logic err_len;
logic offset_val;
logic [5:0] offset_bytes;
logic [5:0] opt_byte_cnt;

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr_done  <= 0;
    receiving <= 0;
    err_len   <= 0;
  end
  else begin
    if (rx.sof && (rx.ipv4_hdr.proto == TCP)) begin
      tcp.mac_hdr  <= rx.mac_hdr;
      tcp.ipv4_hdr <= rx.ipv4_hdr;
      receiving    <= 1;
    end
    if (tcp.eof) receiving <= 0;
    hdr[1:MIN_HDR_LEN-1] <= hdr[0:MIN_HDR_LEN-2];
    if (offset_val && receiving && byte_cnt == offset_bytes) hdr_done <= 1;
    if (receiving && rx.eof && byte_cnt != rx.payload_length) err_len <= !rx.eof;
  end
end

assign tcp.err = (err_len || rx.err);
always @ (posedge clk) fsm_rst <= (tcp.done || rst || tcp.err || tcp.eof);

assign hdr[0] = rx.d;

// Output 

always @ (posedge clk) begin
  if (fsm_rst)  begin
      tcp.d    <= 0;
    tcp.sof  <= 0;
    tcp.eof  <= 0;
    byte_cnt <= 0;
  end
  else begin
    if (rx.v && (rx.ipv4_hdr.proto == TCP)) byte_cnt <= byte_cnt + 1;
    tcp.d <= rx.d;
    tcp.sof <= (offset_val && byte_cnt == offset_bytes && tcp.tcp_hdr.dst_port == dev.tcp_port);
    tcp.eof <= receiving && rx.eof;
  end
end

assign tcp.v = (hdr_done && receiving && (tcp.tcp_hdr.dst_port == dev.tcp_port));

// Latch header
logic opt_en;

tcp_opt_field_t opt_field;
logic [7:0][MAX_TCP_OPT_DATA_LEN-1:0] opt_data;
tcp_opt_t cur_opt;
logic done;

logic [7:0] opt_len;
assign tcp.tcp_hdr_v = tcp.sof; 
logic [5:0] header_len;
assign header_len = hdr[7][7:4] << 2;
always @ (posedge clk) begin
  if (fsm_rst) begin
    tcp.tcp_hdr.src_port     <= 0;
    tcp.tcp_hdr.dst_port     <= 0; 
    tcp.tcp_hdr.tcp_seq_num  <= 0; 
    tcp.tcp_hdr.tcp_ack_num  <= 0; 
    tcp.tcp_hdr.tcp_flags    <= 0;
    tcp.tcp_hdr.tcp_win_size <= 0;
    tcp.tcp_hdr.tcp_chsum <= 0;
    tcp.tcp_hdr.tcp_pointer  <= 0;
    offset_bytes             <= 0;
    opt_len                  <= 0;
    opt_en                   <= 0;
    offset_val               <= 0;
    opt_field                <= opt_field_kind;
  end
  else if (rx.v) begin
    if (byte_cnt == HDR_OPTIONS_POS - 1) begin // Latch Options field timeout get header length
      offset_bytes <= rx.d[7:4] << 2; // multiply by 4
      offset_val <= 1;
    end
    if (byte_cnt == MIN_HDR_LEN - 1) begin
      //$display("-> srv: TCP from %d.%d.%d.%d:%d. Port: %d. Seq: %h. Ack: %h. Offset: %d. Win: %d Pointer: %d",
      //  rx.ipv4_hdr.src_ip[3], 
      //  rx.ipv4_hdr.src_ip[2],
      //  rx.ipv4_hdr.src_ip[1],
      //  rx.ipv4_hdr.src_ip[0],
      //  {hdr[19],hdr[18]},
      //  {hdr[17],hdr[16]},
      //  {hdr[15],hdr[14],hdr[13],hdr[12]},
      //  {hdr[11],hdr[10],hdr[9],hdr[8]},
      //  hdr[7][7:4],
      //  {hdr[5],hdr[4]},
      //  {hdr[1],hdr[0]}
      //);
      //$display("-> srv: TCP flags:");
      //if (hdr[7][0]) $display("-> srv: NS");
      //if (hdr[6][7]) $display("-> srv: CWR");
      //if (hdr[6][6]) $display("-> srv: ECE");
      //if (hdr[6][5]) $display("-> srv: URG");
      //if (hdr[6][4]) $display("-> srv: ACK");
      //if (hdr[6][3]) $display("-> srv: PSH");
      //if (hdr[6][2]) $display("-> srv: RST");
      //if (hdr[6][1]) $display("-> srv: SYN");
      //if (hdr[6][0]) $display("-> srv: FIN");
      tcp.tcp_hdr.src_port     <= {hdr[19], hdr[18]};
      tcp.tcp_hdr.dst_port     <= {hdr[17], hdr[16]};
      tcp.tcp_hdr.tcp_seq_num  <= {hdr[15], hdr[14], hdr[13], hdr[12]};
      tcp.tcp_hdr.tcp_ack_num  <= {hdr[11], hdr[10], hdr[9], hdr[8]};
      tcp.tcp_hdr.tcp_offset   <= hdr[7][7:4];
      tcp.tcp_hdr.reserved     <= 0;
      tcp.tcp_hdr.tcp_flags    <= {hdr[7][0], hdr[6][7:0]};
      tcp.tcp_hdr.tcp_win_size <= {hdr[5],hdr[4]};
      tcp.tcp_hdr.tcp_chsum <= {hdr[3],hdr[2]};
      tcp.tcp_hdr.tcp_pointer  <= {hdr[1],hdr[0]};
      tcp.payload_length <= rx.payload_length - header_len;
      opt_en <= 1; // start analyzing options
    end
    if (opt_en) begin
      case (opt_field)
        opt_field_kind : begin
          case (rx.d)
            TCP_OPT_END : begin
            //  $display("Option kind: end");
              done <= 1;
              opt_field <= opt_field_kind;
              cur_opt <= tcp_opt_end;
            end
            TCP_OPT_NOP : begin
            //  $display("Option kind: NOP");
              opt_field <= opt_field_kind;
              cur_opt <= tcp_opt_nop;
            end
            TCP_OPT_MSS : begin
            //  $display("Option kind: MSS");
              tcp.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
              opt_field <= opt_field_len;
              cur_opt <= tcp_opt_mss;
            end
            TCP_OPT_WIN : begin
            //  $display("Option kind: win");
              tcp.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
              opt_field <= opt_field_len;
              cur_opt <= tcp_opt_win; 
            end
            TCP_OPT_SACK_PERM : begin
            //  $display("Option kind: SACK Permitted");
              tcp.tcp_opt_hdr.tcp_opt_sack_perm.sack_perm_pres <= 1;
              opt_field <= opt_field_len;
              cur_opt <= tcp_opt_sack_perm;
            end
            TCP_OPT_SACK : begin
            //  $display("Option kind: SACK");
              tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres <= 1;
              opt_field <= opt_field_len;
              cur_opt <= tcp_opt_sack;  
            end
            TCP_OPT_TIMESTAMP : begin
            //  $display("Option kind: timestamp");
              tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp_pres <= 1;
              opt_field <= opt_field_len;
              cur_opt <= tcp_opt_timestamp;
            end
            default : begin
              done <= 1;
              opt_field <= opt_field_kind;
            end
          endcase
          opt_byte_cnt <= 0;
        end
        opt_field_len : begin
        //  $display("Option length: %d", rx.d);
          case (rx.d) // Only SACK has variable length
            10      : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 1;
            18      : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 2;
            26      : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 3;
            34      : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 4;
            default : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 0;
          endcase
          opt_len <= rx.d - 2; // exclude kind and length bytes and 1 byte due timeout delay
          opt_field <= (rx.d == 2) ? opt_field_kind : opt_field_data;
        end
        opt_field_data : begin
          if (opt_byte_cnt == opt_len-1) opt_field <= opt_field_kind;
          opt_byte_cnt <= opt_byte_cnt + 1;
        end
      endcase
    end
  end
end

assign opt_data[0] = rx.d;

always @ (posedge clk) begin
  if (fsm_rst) begin
    opt_data[MAX_TCP_OPT_DATA_LEN-1:1] <= 0;
  end
  else begin
    opt_data[MAX_TCP_OPT_DATA_LEN-2:1] <= (opt_field == opt_field_data) ? opt_data[MAX_TCP_OPT_DATA_LEN-1:0] : 0;
    if (opt_byte_cnt == opt_len - 1) begin
      case (cur_opt)
        tcp_opt_mss : begin
        //  $display("MSS Option value: %d", opt_data[1:0]);
          tcp.tcp_opt_hdr.tcp_opt_mss.mss <= opt_data[1:0];
        end
        tcp_opt_win : begin
        //  $display("Window Option value: %d", opt_data[0]);
          tcp.tcp_opt_hdr.tcp_opt_win.win <= opt_data[0];
        end
        tcp_opt_sack : begin
        //  $display("SACK Option value: Begin: %h, End: %h", opt_data[7:4], opt_data[3:0]);
          tcp.tcp_opt_hdr.tcp_opt_sack.sack[0].left  <= opt_data[7:4];
          tcp.tcp_opt_hdr.tcp_opt_sack.sack[0].right <= opt_data[3:0];
          tcp.tcp_opt_hdr.tcp_opt_sack.sack[3:1] <= tcp.tcp_opt_hdr.tcp_opt_sack.sack[2:0];
        end
        tcp_opt_timestamp : begin
          tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp <= opt_data;
        end
      endcase
    end
  end
end

tcp_hdr_t tcp_hdr;
assign tcp_hdr = tcp.tcp_hdr;

endmodule : tcp_vlg_rx
