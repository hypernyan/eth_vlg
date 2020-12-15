import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface tcp;
  logic [7:0]   dat;  // data
  logic         val;  // data valid
  logic         sof;  // start of 'dat' frame
  logic         eof;  // stop of 'dat' frame
  logic         err;  // error
  logic         rdy;  // data ready from to IPv4
  logic         req;  // data request for tx when done with header
  logic         busy; // ipv4 tx busy
  logic         done; // transmission done
  
  tcp_hdr_t     tcp_hdr;
  tcp_opt_hdr_t tcp_opt_hdr;
  logic         tcp_hdr_v;
  ipv4_hdr_t    ipv4_hdr;
  mac_hdr_t     mac_hdr;
  // Packet specific data
  length_t      payload_length;
  logic [31:0]  payload_chsum;
  
  modport in  (input  dat, val, sof, eof, payload_length, payload_chsum, err, tcp_hdr, tcp_opt_hdr, tcp_hdr_v, ipv4_hdr, mac_hdr, rdy, output req, busy, done);
  modport out (output dat, val, sof, eof, payload_length, payload_chsum, err, tcp_hdr, tcp_opt_hdr, tcp_hdr_v, ipv4_hdr, mac_hdr, rdy, input  req, busy, done);
endinterface

interface queue_if #(
  parameter int RAM_WIDTH = 8,
  parameter int RAM_DEPTH = 14
);
  logic                      pend;
  tcp_vlg_pkg::tcp_seq_num_t seq;
  eth_vlg_pkg::length_t      len;
  logic [31:0]               cs;
  logic                      flush; 
  logic                      flushed; 
  logic                      force_fin;  
  logic [RAM_WIDTH-1:0]      data;
  logic [RAM_DEPTH-1:0]      addr;

  modport out     (output pend, seq, len, cs, flushed, force_fin, input  flush);
  modport in      (input  pend, seq, len, cs, flushed, force_fin, output flush);
  modport out_ram (output data, input addr);
  modport in_ram  (input  data, output addr);
endinterface : queue_if

module tcp_vlg #(
  parameter int MTU              = 1500,
  parameter int MAX_PAYLOAD_LEN  = 1400,
  parameter int RETRANSMIT_TICKS = 1000000,
  parameter int RETRANSMIT_TRIES = 5,
  parameter int RAM_DEPTH        = 12,
  parameter int PACKET_DEPTH     = 8,
  parameter int WAIT_TICKS       = 100,
  parameter bit VERBOSE          = 0
)
(
  input logic clk,
  input logic rst,

  input  dev_t  dev,
  input  port_t port,

  ipv4.in_rx  rx,
  ipv4.out_tx tx,

  input  logic [7:0] din,
  input  logic       vin,
  output logic       cts,
  input  logic       snd,

  output logic [7:0] dout,
  output logic       vout,

  output logic  connected,
  input  logic  connect, 
  input  logic  listen,  
  input  ipv4_t rem_ipv4,
  input  port_t rem_port
);

tcp tcp_tx(.*);
tcp tcp_rx(.*);

tcb_t tcb;

queue_if #($bits(byte), RAM_DEPTH) queue_ram (.*);
queue_if #($bits(byte), RAM_DEPTH) queue     (.*);

tcp_vlg_rx tcp_vlg_rx_inst (  
  .clk  (clk),
  .rst  (rst),
  .port (port),
  .ipv4 (rx), // ipv4
  .tcp  (tcp_rx) // stripped from ipv4, raw tcp
);

tcp_vlg_engine #(
  .VERBOSE (VERBOSE)
) tcp_vlg_engine_inst (
  .clk           (clk),
  .rst           (rst),
  .dev           (dev),
  .port          (port),
  .tcb           (tcb),
  .rx            (tcp_rx),
  .tx            (tcp_tx),     // server -> tx
  .vout          (vout),  //in. packet ready in queue
  .dout          (dout),  //in. packet ready in queue
  .queue         (queue),
  // tcp control
  .connected     (connected),  // this flag indicated connection status as well as selects header to pass to tcp_tx
  .connect       (connect), 
  .listen        (listen),  
  .rem_ipv4      (rem_ipv4),
  .rem_port      (rem_port)
);

tcp_vlg_tx_queue #(
  .MTU              (MTU),
  .MAX_PAYLOAD_LEN  (MAX_PAYLOAD_LEN),
  .RETRANSMIT_TICKS (RETRANSMIT_TICKS),
  .RETRANSMIT_TRIES (RETRANSMIT_TRIES),
  .RAM_DEPTH        (RAM_DEPTH),
  .PACKET_DEPTH     (PACKET_DEPTH),
  .WAIT_TICKS       (WAIT_TICKS)
) tcp_vlg_tx_queue_inst (
  .clk           (clk),
  .rst           (rst),
  .dev           (dev),
    // user interface
  .in_d          (din),
  .in_v          (vin),
  .cts           (cts),
  .snd           (snd),
  .connected     (connected),
  // tcp tx status
  .tx_busy       (tcp_tx.busy),
  .tx_done       (tcp_tx.done),

  .tcb           (tcb),
  .queue         (queue),
  .queue_ram     (queue_ram)
);

tcp_vlg_tx #(
  .RAM_DEPTH (RAM_DEPTH)
) tcp_vlg_tx_inst (  
  .clk           (clk),
  .rst           (rst),
  .ipv4          (tx),
  .tcp           (tcp_tx),
  .queue_ram     (queue_ram),
  .req           ()
);

endmodule

module tcp_vlg_rx (
  input logic  clk,
  input logic  rst,
  input port_t port,
  ipv4.in_rx   ipv4,
  tcp.out      tcp
);

logic [15:0] byte_cnt;
logic        fsm_rst;

logic [0:tcp_vlg_pkg::TCP_HDR_LEN-1][7:0] hdr;

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
    if (ipv4.sof && (ipv4.ipv4_hdr.proto == TCP)) begin
      tcp.mac_hdr  <= ipv4.mac_hdr;
      tcp.ipv4_hdr <= ipv4.ipv4_hdr;
      receiving    <= 1;
    end
    if (tcp.eof) receiving <= 0;
    hdr[1:tcp_vlg_pkg::TCP_HDR_LEN-1] <= hdr[0:tcp_vlg_pkg::TCP_HDR_LEN-2];
    if (offset_val && receiving && byte_cnt == offset_bytes) hdr_done <= 1;
    if (receiving && ipv4.eof && byte_cnt != ipv4.payload_length) err_len <= !ipv4.eof;
  end
end

assign tcp.err = (err_len || ipv4.err);
always @ (posedge clk) fsm_rst <= (tcp.done || rst || tcp.err || tcp.eof);

assign hdr[0] = ipv4.dat;

// Output 

always @ (posedge clk) begin
  if (fsm_rst)  begin
    tcp.dat  <= 0;
    tcp.sof  <= 0;
    tcp.eof  <= 0;
    byte_cnt <= 0;
  end
  else begin
    if (ipv4.val && (ipv4.ipv4_hdr.proto == TCP)) byte_cnt <= byte_cnt + 1;
    tcp.dat <= ipv4.dat;
    tcp.sof <= (receiving && offset_val && byte_cnt == offset_bytes && tcp.tcp_hdr.dst_port == port);
    tcp.eof <= receiving && ipv4.eof;
  end
end

assign tcp.val = (hdr_done && receiving && (tcp.tcp_hdr.dst_port == port));

// Latch header
logic opt_en;

tcp_opt_field_t opt_field;
logic [7:0][tcp_vlg_pkg::OPT_LEN-1:0] opt_data;
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
    tcp.tcp_hdr.tcp_chsum    <= 0;
    tcp.tcp_hdr.tcp_pointer  <= 0;
    offset_bytes             <= 0;
    opt_len                  <= 0;
    opt_en                   <= 0;
    offset_val               <= 0;
    opt_field                <= tcp_opt_field_kind;
  end
  else if (ipv4.val) begin
    if (byte_cnt == tcp_vlg_pkg::HDR_OPTIONS_POS - 1) begin // Latch Options field timeout get header length
      offset_bytes <= ipv4.dat[7:4] << 2; // multiply by 4
      offset_val <= 1;
    end
    if (byte_cnt == tcp_vlg_pkg::TCP_HDR_LEN - 1) begin
      //$display("-> srv: TCP from %d.%d.%d.%d:%d. Port: %d. Seq: %h. Ack: %h. Offset: %d. Win: %d Pointer: %d",
      //  ipv4.ipv4_hdr.src_ip[3], 
      //  ipv4.ipv4_hdr.src_ip[2],
      //  ipv4.ipv4_hdr.src_ip[1],
      //  ipv4.ipv4_hdr.src_ip[0],
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
      tcp.payload_length <= ipv4.payload_length - header_len;
      opt_en <= 1; // start analyzing options
    end
    if (opt_en) begin
      case (opt_field)
        tcp_opt_field_kind : begin
          case (ipv4.dat)
            TCP_OPT_END : begin
            //  $display("Option kind: end");
              done <= 1;
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
              tcp.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
              opt_field <= tcp_opt_field_len;
              cur_opt <= tcp_opt_mss;
            end
            TCP_OPT_WIN : begin
            //  $display("Option kind: win");
              tcp.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
              opt_field <= tcp_opt_field_len;
              cur_opt <= tcp_opt_win; 
            end
            TCP_OPT_SACK_PERM : begin
            //  $display("Option kind: SACK Permitted");
              tcp.tcp_opt_hdr.tcp_opt_sack_perm.sack_perm_pres <= 1;
              opt_field <= tcp_opt_field_len;
              cur_opt <= tcp_opt_sack_perm;
            end
            TCP_OPT_SACK : begin
            //  $display("Option kind: SACK");
              tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres <= 1;
              opt_field <= tcp_opt_field_len;
              cur_opt <= tcp_opt_sack;  
            end
            TCP_OPT_TIMESTAMP : begin
            //  $display("Option kind: timestamp");
              tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp_pres <= 1;
              opt_field <= tcp_opt_field_len;
              cur_opt <= tcp_opt_timestamp;
            end
            default : begin
              done <= 1;
              opt_field <= tcp_opt_field_kind;
            end
          endcase
          opt_byte_cnt <= 0;
        end
        tcp_opt_field_len : begin
        //  $display("Option length: %d", ipv4.d);
          case (ipv4.dat) // Only SACK has variable length
            10      : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 1;
            18      : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 2;
            26      : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 3;
            34      : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 4;
            default : tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks <= 0;
          endcase
          opt_len <= ipv4.dat - 2; // exclude kind and length bytes and 1 byte due timeout delay
          opt_field <= (ipv4.dat == 2) ? tcp_opt_field_kind : tcp_opt_field_data;
        end
        tcp_opt_field_data : begin
          if (opt_byte_cnt == opt_len-1) opt_field <= tcp_opt_field_kind;
          opt_byte_cnt <= opt_byte_cnt + 1;
        end
      endcase
    end
  end
end

assign opt_data[0] = ipv4.dat;

always @ (posedge clk) begin
  if (fsm_rst) begin
    opt_data[tcp_vlg_pkg::OPT_LEN-1:1] <= 0;
  end
  else begin
    opt_data[tcp_vlg_pkg::OPT_LEN-2:1] <= (opt_field == tcp_opt_field_data) ? opt_data[tcp_vlg_pkg::OPT_LEN-1:0] : 0;
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

module tcp_vlg_tx #(
  parameter int RAM_DEPTH = 10
)(
  input logic      clk,
  input logic      rst,
  tcp.in           tcp,
  ipv4.out_tx      ipv4,
  queue_if.in_ram  queue_ram,
  output logic     req //out.
);

localparam MIN_TCP_HDR_LEN = 20;
localparam MAX_TCP_HDR_LEN = 60;
localparam HDR_OPTIONS_POS = 13;

tcp_hdr_t cur_tcp_hdr;

logic fsm_rst;
logic [15:0] byte_cnt;
logic [0:MAX_TCP_HDR_LEN-1][7:0] hdr, hdr_calc;
logic transmitting;
logic hdr_done;
logic done, opt_assembled;

logic [31:0] pseudo_hdr_chsum, hdr_chsum;

logic calc, calc_done;
logic [0:39][7:0] opt_hdr;
logic [0:11][7:0] pseudo_hdr;
logic [19:0][7:0] tcp_tcp_hdr;

logic [31:0] chsum_carry;
logic [15:0] calc_cnt;
logic [15:0] chsum;

assign ipv4.ipv4_hdr = tcp.ipv4_hdr;

logic [16:0] chsum_summ; // extra bit for sum's carry

assign chsum_summ[16:0] = chsum_carry[31:16] + chsum_carry[15:0]; // Calculate actual chsum
assign chsum = ~ (chsum_summ[15:0] + chsum_summ[16]);

logic [15:0] pseudo_hdr_pkt_len;
assign pseudo_hdr_pkt_len = (tcp.ipv4_hdr.length - 20);

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr              <= 0;
    hdr_done         <= 0;
   // ipv4.sof         <= 0;
    ipv4.eof         <= 0;
    ipv4.val         <= 0;
    transmitting     <= 0;
    byte_cnt         <= 0;
    pseudo_hdr_chsum <= 0;
    hdr_chsum        <= 0;
    calc             <= 0;
    calc_done        <= 0;
    calc_cnt         <= 0;
    chsum_carry      <= 0;
    tcp.req          <= 0;
    pseudo_hdr       <= 0;
    req              <= 0;
    cur_tcp_hdr      <= 0;
    queue_ram.addr   <= 0;
    ipv4.broadcast   <= 0;
    ipv4.rdy         <= 0;
  end
  else begin
    if (tcp.tcp_hdr_v) cur_tcp_hdr <= tcp.tcp_hdr;
    if (ipv4.val) byte_cnt <= byte_cnt + 1; // count outcoming bytes
    //ipv4.sof <= (calc_done && !transmitting); // assert sof when done calculating chsum 
    if (opt_assembled && !calc) begin // wait for options to be assembled, latch them for chsum calculation
      hdr_calc <= {cur_tcp_hdr, opt_hdr}; // concat header from tcp header and options
      pseudo_hdr <= {tcp.ipv4_hdr.src_ip, tcp.ipv4_hdr.dst_ip, 8'h0, TCP, pseudo_hdr_pkt_len}; // assemble pseudo header
      chsum_carry <= tcp.payload_chsum; // initialize chsum with payload chsum
      calc <= 1;
    end
    else if (calc) begin // chsum is calculated here
      calc_cnt <= calc_cnt + 1;
      pseudo_hdr[0:9] <= pseudo_hdr[2:11]; // shift tcp header and options by 16 bits
      hdr_calc[0:MAX_TCP_HDR_LEN-3] <= hdr_calc[2:MAX_TCP_HDR_LEN-1];
      pseudo_hdr_chsum <= pseudo_hdr_chsum + pseudo_hdr[0:1]; // Pseudo header checksum calculation
      hdr_chsum <= hdr_chsum + hdr_calc[0:1]; // TCP header checksum calculation
      if (calc_cnt == 6) chsum_carry <= chsum_carry + pseudo_hdr_chsum; // Pseudo header length is 12 bytes (6 ticks by 16 bits)
      else if (calc_cnt == (cur_tcp_hdr.tcp_offset << 1)) begin // Header has variable length, calc takes variable amount of ticks
        chsum_carry <= chsum_carry + hdr_chsum;
        calc_done <= 1;
      end
    end
    ipv4.rdy <= (calc_done && opt_assembled);
    if (ipv4.rdy && ipv4.req && !transmitting) begin
      transmitting <= 1; // Start transmitting now
      ipv4.val <= 1;
      // Assemble header to be transmitted
      hdr[0:1]     <= cur_tcp_hdr.src_port;
      hdr[2:3]     <= cur_tcp_hdr.dst_port;
      hdr[4:7]     <= cur_tcp_hdr.tcp_seq_num;
      hdr[8:11]    <= cur_tcp_hdr.tcp_ack_num;
      hdr[12][7:4] <= cur_tcp_hdr.tcp_offset;
      {hdr[12][0], hdr[13][7:0]} <= cur_tcp_hdr.tcp_flags;
      hdr[14:15]   <= cur_tcp_hdr.tcp_win_size;
      hdr[16:17]   <= chsum; // Checksum needs to be ready at byte 16
      hdr[18:19]   <= cur_tcp_hdr.tcp_pointer;
      hdr[MIN_TCP_HDR_LEN:MAX_TCP_HDR_LEN-1] <= opt_hdr;
    end
    else if (transmitting) hdr[0:MAX_TCP_HDR_LEN-2] <= hdr[1:MAX_TCP_HDR_LEN-1];
    if (transmitting && byte_cnt == ((cur_tcp_hdr.tcp_offset << 2) - 2) && tcp.payload_length != 0) begin
      req <= 1;
    end
    if (req) hdr_done <= 1;
    if (tcp.tcp_hdr_v) queue_ram.addr <= tcp.tcp_hdr.tcp_seq_num;
    else if (req) queue_ram.addr <= queue_ram.addr + 1;
    if (byte_cnt == tcp.ipv4_hdr.length - 22) ipv4.eof <= 1;
  end
end
assign ipv4.sof = (byte_cnt == 0) && transmitting;
assign ipv4.dat = (hdr_done) ? queue_ram.data : hdr[0]; // mux output between header and data from server

assign tcp.done = ipv4.done;
assign fsm_rst = (ipv4.eof || rst);

logic [7:0] tcp_sack_len;
tcp_opt_t   opt;

assign tcp_sack_len = (tcp.tcp_opt_hdr.tcp_opt_sack.sack_blocks << 3) + 2;

logic [0:14][31:0] opt_hdr_proto;
logic [0:14]       opt_hdr_pres;

logic cur_opt_pres, shift_opt, tcp_opt_done;
logic [3:0] opt_cnt;
logic [3:0] opt_len_32;
logic busy;
assign tcp.busy = (busy || ipv4.busy);

// FSM to generate TCP options header
// tcp_hdr_v to opt_assembled delay:
// - 128 ns
// - 16 ticks

always @ (posedge clk) begin
  if (fsm_rst) begin
    opt           <= tcp_opt_mss;
    opt_cnt       <= 0;
    opt_hdr_pres  <= 0;
    opt_hdr_proto <= 0;
    opt_len_32    <= 0;
    opt_assembled <= 0;
    shift_opt     <= 0;
    busy          <= 0;
  end
  else begin
    if (tcp.tcp_hdr_v) begin
      busy <= 1;  // set busy flag and reset it when done transmitting. Other server and queue instances will wait for sending next packet 
      shift_opt <= 1; // After options and header are set, compose a valid option header
      opt_hdr_proto <= {
        tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp.snd,
        tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp.rec,
        {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_TIMESTAMP, 8'd10},
        tcp.tcp_opt_hdr.tcp_opt_sack.sack[3].right,
        tcp.tcp_opt_hdr.tcp_opt_sack.sack[3].left,
        tcp.tcp_opt_hdr.tcp_opt_sack.sack[2].right,
        tcp.tcp_opt_hdr.tcp_opt_sack.sack[2].left,
        tcp.tcp_opt_hdr.tcp_opt_sack.sack[1].right,
        tcp.tcp_opt_hdr.tcp_opt_sack.sack[1].left,
        tcp.tcp_opt_hdr.tcp_opt_sack.sack[0].right,
        tcp.tcp_opt_hdr.tcp_opt_sack.sack[0].left,
        {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_SACK, tcp_sack_len},
        {TCP_OPT_NOP, TCP_OPT_NOP, TCP_OPT_SACK_PERM, 8'd2},
        {TCP_OPT_NOP, TCP_OPT_WIN, 8'd3, tcp.tcp_opt_hdr.tcp_opt_win.win},
        {TCP_OPT_MSS, 8'd4, tcp.tcp_opt_hdr.tcp_opt_mss.mss[1], tcp.tcp_opt_hdr.tcp_opt_mss.mss[0]}
      }; // Option header prototype. Fill it with all possible options
      opt_hdr_pres <= {
        {3{tcp.tcp_opt_hdr.tcp_opt_timestamp.timestamp_pres}},
        {2{tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres && tcp.tcp_opt_hdr.tcp_opt_sack.block_pres[3]}},
        {2{tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres && tcp.tcp_opt_hdr.tcp_opt_sack.block_pres[2]}},
        {2{tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres && tcp.tcp_opt_hdr.tcp_opt_sack.block_pres[1]}},
        {2{tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres && tcp.tcp_opt_hdr.tcp_opt_sack.block_pres[0]}},
        tcp.tcp_opt_hdr.tcp_opt_sack.sack_pres,
        tcp.tcp_opt_hdr.tcp_opt_sack_perm.sack_perm_pres,
        tcp.tcp_opt_hdr.tcp_opt_win.win_pres,
        tcp.tcp_opt_hdr.tcp_opt_mss.mss_pres
      }; // Set which option fields are present
    end
    else if (shift_opt) begin // Create valid options to concat it with tcp header
      opt_cnt <= opt_cnt + 1;
      opt_hdr_proto[0:13] <= opt_hdr_proto[1:14];
      opt_hdr_pres[0:13] <= opt_hdr_pres[1:14];
      if (opt_hdr_pres[0]) begin // Shift by 32 bits
        opt_len_32 <= opt_len_32 + 1;
        opt_hdr[0:3] <= opt_hdr_proto[0];
        opt_hdr[4:39] <= opt_hdr[0:35];
      end
      if (opt_cnt == 14 || cur_tcp_hdr.tcp_offset == 5) begin // If done shifting or packet has no options
        opt_assembled <= 1;
        shift_opt <= 0;
      end
    end
  end
end

assign opt_len = opt_len_32 << 2;

endmodule : tcp_vlg_tx

module tcp_vlg_engine #(
  parameter int MTU                      = 1500,
  parameter int CONNECTION_TIMEOUT_TICKS = 10000000,
  parameter int ACK_TIMEOUT              = 125000,
  parameter int KEEPALIVE_PERIOD         = 125000000,
  parameter bit ENABLE_KEEPALIVE         = 1,
  parameter int KEEPALIVE_TRIES          = 5,
  parameter bit VERBOSE                  = 0
)
(
  input logic         clk,
  input logic         rst,
  input dev_t         dev,
  input port_t        port,
  output tcb_t        tcb,
  tcp.in              rx,
  tcp.out             tx,
  output logic        vout,
  output logic [7:0]  dout,
  
  queue_if.in         queue,

  output logic        connected,
  input  logic        connect, 
  input  logic        listen,  
  input  ipv4_t       rem_ipv4,
  input  port_t       rem_port
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

logic [31:0] ipv4_id_prng, seq_num_prng;

prng prng_ipv4_id_inst (
  .clk (clk),
  .rst (rst),
  .in  (1'b0),
  .res (ipv4_id_prng)
);

prng prng_seq_num_inst (
  .clk (clk),
  .rst (rst),
  .in  (1'b0),
  .res (seq_num_prng)
);

always @ (posedge clk) tcp_rst <= rst || (connection_timeout == CONNECTION_TIMEOUT_TICKS) || fin_rst;

always @ (posedge clk) begin
  if (tcp_rst) begin
    tcp_fsm            <= tcp_closed_s;
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
    queue.flush        <= 0;
    valid_rx           <= 0;
    connection_type    <= tcp_client;
    force_ack          <= 0;
    keepalive_fin      <= 0;
    keepalive_tries    <= 0;
    tx.ipv4_hdr.dst_ip <= 0;
    tx.ipv4_hdr.id     <= 0;
    tx.ipv4_hdr.length <= 0;
    tx.ipv4_hdr.dst_ip <= 0;
  end
  else begin
    rxv_reg <= rx.val;
    rxd_reg <= rx.dat;
    if (!((tcp_fsm == tcp_closed_s) || (tcp_fsm == tcp_listen_s) || (tcp_fsm == tcp_established_s))) connection_timeout <= connection_timeout + 1;
    case (tcp_fsm)
      tcp_closed_s : begin
        queue.flush <= 0;
        tx.payload_length <= 0;
        if (listen) begin // transition to listen aka server mode
          connection_type <= tcp_server; // define future connection type
          tcp_fsm <= tcp_listen_s;
        end
        else if (connect) begin
          connection_type <= tcp_client;
          // Basic options
          tx.tcp_opt_hdr.tcp_opt_win.win_pres <= 1;
          tx.tcp_opt_hdr.tcp_opt_win.win      <= 8;
          tx.tcp_opt_hdr.tcp_opt_mss.mss_pres <= 1;
          tx.tcp_opt_hdr.tcp_opt_mss.mss      <= 8960;
          // Set relevant IP header fields for transmission
          tx.ipv4_hdr.dst_ip <= rem_ipv4;
          tx.ipv4_hdr.id     <= ipv4_id_prng;
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
          tcb.loc_seq_num  <= seq_num_prng;
          if (tcb_created) begin
            if (VERBOSE) $display("%d.%d.%d.%d:%d-> [SYN] to %d.%d.%d.%d:%d Seq=%h Ack=%h",
              dev.ipv4_addr[3],dev.ipv4_addr[2],dev.ipv4_addr[1],dev.ipv4_addr[0],port,
              tx.ipv4_hdr.dst_ip[3],rx.ipv4_hdr.dst_ip[2],rx.ipv4_hdr.dst_ip[1],rx.ipv4_hdr.dst_ip[0],
              tx.tcp_hdr.dst_port, tx.tcp_hdr.tcp_seq_num, tx.tcp_hdr.tcp_ack_num
            );
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
          if (VERBOSE) $display("%d.%d.%d.%d:%d<- [SYN, ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
            dev.ipv4_addr[3],dev.ipv4_addr[2],dev.ipv4_addr[1],dev.ipv4_addr[0],port,
            rx.ipv4_hdr.src_ip[3],rx.ipv4_hdr.src_ip[2],rx.ipv4_hdr.src_ip[1],rx.ipv4_hdr.src_ip[0],
            rx.tcp_hdr.src_port,rx.tcp_hdr.tcp_seq_num,rx.tcp_hdr.tcp_ack_num
          );
        //  connected <= 1;
          tcp_fsm <= tcp_established_s;
          tx.ipv4_hdr.id     <= tx.ipv4_hdr.id + 1;
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
        tx.tcp_opt_hdr.tcp_opt_mss.mss      <= MTU - 40;
        if (rx.tcp_hdr_v && rx.tcp_hdr.tcp_flags.syn && (rx.tcp_hdr.dst_port == port)) begin // connection request
          // ipv4 header
          tx.ipv4_hdr.dst_ip <= rx.ipv4_hdr.src_ip;
          tx.ipv4_hdr.id     <= rx.ipv4_hdr.id + 1;
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
          tcb.loc_seq_num <= seq_num_prng;
          tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
          tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
          if (VERBOSE) $display("%d.%d.%d.%d:%d<- [SYN] from %d.%d.%d.%d:%d Seq=%h Ack=%h",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], port,
            rx.ipv4_hdr.src_ip[3],rx.ipv4_hdr.src_ip[2],rx.ipv4_hdr.src_ip[1], rx.ipv4_hdr.src_ip[0],
            rx.tcp_hdr.src_port, rx.tcp_hdr.tcp_seq_num, rx.tcp_hdr.tcp_ack_num
          );
        end
        if (tcb_created) begin // Once TCB fields are filled, continue
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
            if (VERBOSE) $display("%d.%d.%d.%d:%d<- [ACK] from %d.%d.%d.%d:%d Seq=%h Ack=%h. Connection established",
              dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], port,
		          rx.ipv4_hdr.src_ip[3],rx.ipv4_hdr.src_ip[2],rx.ipv4_hdr.src_ip[1], rx.ipv4_hdr.src_ip[0], rx.tcp_hdr.src_port,
              rx.tcp_hdr.tcp_seq_num, rx.tcp_hdr.tcp_ack_num);
            tcp_fsm <= tcp_established_s;
          // connected <= 1;
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
        if (queue.pend && !tx.busy) begin // if queue has something
          tcb.loc_seq_num        <= queue.seq + queue.len;
          tx.payload_chsum       <= queue.cs;
          tx.payload_length      <= queue.len;
          tx.ipv4_hdr.dst_ip     <= tcb.ipv4_addr;
          tx.ipv4_hdr.length     <= 20 + 20 + queue.len; // 20 for tcp header, 20 for ipv4 header
          tx.tcp_hdr.tcp_seq_num <= queue.seq; // get seq number from queue
          tx.tcp_hdr.tcp_ack_num <= tcb.loc_ack_num; // get local ack from TCB
          tx.tcp_hdr.tcp_flags   <= 9'h018; // PSH ACK
          tx.tcp_hdr_v           <= 1;
          if (!tx.tcp_hdr_v && VERBOSE) $display("%d.%d.%d.%d:%d-> Transmit seq:%h,len:%d,ack:%h", 
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], port, queue.seq, queue.len, tcb.loc_ack_num);
        end
        else if ((keepalive_ack || force_ack) && !tx.busy) begin // If currently remote seq != local ack, force ack w/o data
          $display("%d.%d.%d.%d:%d Ack timeout (seq:%h, ack:%h)",
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
          if (VERBOSE) $display("%d.%d.%d.%d:%d<- Received seq:%h,len:%d,loc ack:%h",
            dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0],
            rx.tcp_hdr.src_port, rx.tcp_hdr.tcp_seq_num, rx.payload_length, tcb.loc_ack_num + rx.payload_length);
          valid_rx <= 1;
          tcb.rem_seq_num <= rx.tcp_hdr.tcp_seq_num;
          tcb.rem_ack_num <= rx.tcp_hdr.tcp_ack_num;
          tcb.loc_ack_num <= tcb.loc_ack_num + (rx.payload_length);
          //tcb.sack <= rx.
          if (rx.payload_length != 0) ack_timer <= 0; // Exclude 0-length packets: avoid Keepalive lock
          keepalive_tries <= 0;
          keepalive_timer <= 0;
        end
        else begin
          if (!rx.val) valid_rx <= 0;
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
        if (keepalive_fin || queue.force_fin || ((connection_type == tcp_client) && !connect) || ((connection_type == tcp_server) && !listen)) begin
          queue.flush <= 1;
          close <= close_active;
        end
        // if remote side wishes to close connection, go with passive close
        else if (conn_filter && rx.tcp_hdr.tcp_flags.fin) begin 
          queue.flush <= 1;
          close <= close_passive;
        end
		    // if rst flag received, skip connection termination
        else if (conn_filter && rx.tcp_hdr.tcp_flags.rst) begin
          queue.flush <= 1;
          close <= close_reset;
        end
        // either way, memory in tx queue should be flushed because RAM contents can't be simply reset
		    // it is necessary to flush it for future connections
        // So wait till queue is flushed...
        if (queue.flushed) begin
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

endmodule : tcp_vlg_engine

/* manage queue.data queuing, retransmissions and chsum calculation
   incoming queue.data is stored in RAM of size 2^RAM_DEPTH
   if user doesn't send queue.data for WAIT_TICKS or MAX_PAYLOAD_LEN is reached with no interruptions in in_v, 
   packed is queued and an entry in fifo_queue_ram is added. 
   Each entry contains info necessary for server and tx module to send user queue.data:
     - present flag which indicates that the packet is unacked and is still queued
     - chsum for this payload
     - queue.seq - start address for the packet in raw queue.data buffer
     - length of the packet ecpressed in bytes
     - timer - timer to retransmit unacked packets
     - tries - times server has tried to retransmit the packet

.                     ________                      _____
.                    |raw queue.data|===read packet=====>|     |
.                    |  RAM   |                    |     |
.                    |        |                    |TCP  |
.                    | port B |                    | tx  |                 
.                    |        | tx                 |     |                 
.                    | port A |======>             |_____|  
.                    |________|                                 
.                     _________    ________   tx         
.                    | port A  |=>|  scan  |=======> 
.                    |__(add)__|<=|  FSM   |queue.pend 
.                    | packet  |  |________|  
.         ______     |  info   |
.        |      |    |  RAM    |
.        | new  |    |_________|     
.        |packet|===>| port B  |  
.        |adder |    |_(clear)_|
         |______|               
*/

module tcp_vlg_tx_queue #(
  parameter integer MTU              = 1500, // Maximum payload length
  parameter integer MAX_PAYLOAD_LEN  = 1400, // Maximum payload length
  parameter integer RETRANSMIT_TICKS = 1000000,
  parameter integer RETRANSMIT_TRIES = 5,
  parameter integer RAM_DEPTH        = 10,
  parameter integer PACKET_DEPTH     = 3,
  parameter integer WAIT_TICKS       = 20
)
(
  input   logic       clk,
  input   logic       rst,

  input   dev_t       dev,

  input   logic [7:0] in_d,
  input   logic       in_v,
  output  logic       cts,
  input   logic       snd,
  input   logic       tx_busy,
  input   logic       tx_done,
  input   tcb_t       tcb,
  queue_if.out        queue,
  queue_if.out_ram    queue_ram,
  input  logic        connected
);

tcp_pkt_t upd_pkt, upd_pkt_q, new_pkt, new_pkt_q;

logic [PACKET_DEPTH-1:0] new_addr, upd_addr, upd_addr_prev;
logic [$clog2(MAX_PAYLOAD_LEN+1)-1:0] ctr;
logic [$clog2(WAIT_TICKS+1)-1:0] timeout;
logic [31:0] chsum;
logic [31:0] cur_seq, ack_diff, ack, stop, start;
logic [RAM_DEPTH-1:0] space_left;
logic [7:0] in_d_prev;
logic in_v_prev;
logic connected_prev, load_pend;

logic fifo_rst, upd_cts, load, upd, chsum_rst;

logic free, retrans;
logic [$clog2(RETRANSMIT_TICKS+1)+RETRANSMIT_TRIES:0] timer;
logic [7:0] tries;

tcp_data_queue #(
  .D (RAM_DEPTH),
  .W (8)
) tcp_data_queue_inst (
  .rst (fifo_rst),
  .clk (clk),
 
  .w_v (in_v),
  .w_d (in_d),
  .seq (cur_seq),
  .isn (tcb.loc_seq_num),
  .space_left (space_left),
  .rd_addr (queue_ram.addr),
  .ack (ack),
  .r_q (queue_ram.data),

  .f (full),
  .e (empty)
);

// raw tcp queue.data is kept here
//fifo_queue_ram #(PACKET_DEPTH) fifo_queue_ram_inst (.*);

ram_if_dp #(
  .AW (PACKET_DEPTH),
  .DW ($bits(tcp_pkt_t))
) data_ram (.*);

ram_dp #(
  .AW (PACKET_DEPTH),
  .DW ($bits(tcp_pkt_t))
) data_ram_inst (data_ram);

assign data_ram.clk_a = clk;              
assign data_ram.clk_b = clk;              
assign data_ram.rst   = rst;              
assign data_ram.a_a   = new_addr;              
assign data_ram.a_b   = upd_addr;              
assign data_ram.d_a   = new_pkt;              
assign data_ram.d_b   = upd_pkt;              
assign data_ram.w_a   = load;              
assign data_ram.w_b   = upd;              
assign new_pkt_q      = data_ram.q_a;              
assign upd_pkt_q      = data_ram.q_b;              

logic [PACKET_DEPTH:0] new_ptr, new_ptr_ahead, free_ptr, diff, flush_ctr;

assign diff = new_ptr_ahead - free_ptr;
assign cts = connected && !diff[PACKET_DEPTH] && !full;

assign new_addr[PACKET_DEPTH-1:0] = new_ptr[PACKET_DEPTH-1:0];

enum logic {
  w_idle_s,
  w_pend_s
} w_fsm;

logic load_timeout, load_mtu, load_full;

always @ (posedge clk) begin
  connected_prev <= connected;
  fifo_rst <= rst || (connected_prev != connected);
end

assign load_timeout = (timeout == WAIT_TICKS && !in_v);
assign load_mtu     = (ctr == MAX_PAYLOAD_LEN);
assign load_full    = full;

assign load_pend = (w_fsm == w_pend_s) && (load_timeout || load_mtu || load_full || snd);   
assign new_pkt.length  = ctr; // length equals byte count for current packet. together with queue.seq logic reads out facket from fifo
assign new_pkt.chsum   = ctr[0] ? chsum + {in_d_prev, 8'h00} : chsum;
assign new_pkt.present = 1; // this packet is pendingid in memory
assign new_pkt.tries   = 0; // haven't tried to transmit the packet
assign new_pkt.sacked  = 0; // create an unSACKed packet
assign new_pkt.timer   = RETRANSMIT_TICKS; // preload so packet is read out asap the first time
assign new_pkt.stop    = cur_seq; // equals expected ack for packet

always @ (posedge clk) begin
  if (fifo_rst || queue.flush) begin
    ctr     <= 0;
    new_ptr <= 0;
    load    <= 0;
    timeout <= 0;
    cur_seq <= tcb.loc_seq_num;
    w_fsm <= w_idle_s;
  end
  else begin
    new_pkt.start <= cur_seq - ctr; // equals packet's queue.seq
    if (in_v) begin
      in_d_prev <= in_d;
      cur_seq <= cur_seq + 1;
    end
    case (w_fsm)
      w_idle_s : begin
        if (in_v) w_fsm <= w_pend_s;
        ctr <= 1; // Can't add packet with zero length
        load <= 0;
        chsum <= 0;
        timeout <= 0;
      end
      w_pend_s : begin // queue.pend load
        if (in_v) begin
          ctr <= ctr + 1;
          chsum <= (ctr[0]) ? chsum + {in_d_prev, in_d} : chsum;
        end
        timeout <= (in_v) ? 0 : timeout + 1; // reset timeout if new byte arrives
        // either of three conditions to load new pakcet
        if (load_full || load_timeout || load_mtu || snd) w_fsm <= w_idle_s;
      end
    endcase
    load <= load_pend; // load packet 1 tick after 'queue.pend'
//    if (load) $display("%d.%d.%d.%d:%d: Queuing packet: queue.seq:%h,nxt queue.seq:%h, queue.len:%d. space: %d", dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0], dev.tcp_port, cur_seq - ctr, cur_seq, ctr, space_left);
    if (load) new_ptr <= new_ptr + 1;
    new_ptr_ahead <= new_ptr + 1;
  end
end

enum logic [6:0] {
  queue_scan_s,
  queue_check_s,
  queue_read_s,
  queue_next_s,
  queue_wait_s,
  queue_retrans_s,
  queue_flush_s
} fsm;

// remote host may acknowledge some part of the packet (mainly when sending queue.data of length > remote host window)
// queue RAM frees space based on ack_num
// have to check if received ack_num acknowledges whole packet, otherwise queue.data may be overwritten and checksum will be incorrect
// pass packet's expected ack instead of remote ack
// this is neded to avoid repacketisation

// - free space                p s      r a          p a
// = valid queue.data          k e      e c          k c
// x overwritten queue.data    t q      m k          t k
// -----------------------------|========|============|-------- 
// -----------------------------|========|xxxxxxxxxxxx|-------- queue.data loss if remote ack is passed directly to queue RAM

always @ (posedge clk) begin
  if (fifo_rst) begin // Engine has to close connection to reenable queue
    fsm             <= queue_scan_s;
    upd             <= 0;
    upd_addr        <= 0;
    queue.force_fin <= 0;
    queue.pend      <= 0;
    free_ptr        <= 0;
    flush_ctr       <= 0;
    queue.flushed   <= 0;
    upd_pkt         <= 0;
	  ack             <= tcb.rem_ack_num;
    tries           <= 0;
    timer           <= 0;
    free            <= 0;
  end
  else begin
	  queue.cs       <= upd_pkt_q.chsum;
    // don't change these fields:
    upd_pkt.chsum  <= upd_pkt_q.chsum;
    upd_pkt.start  <= upd_pkt_q.start;
    upd_pkt.stop   <= upd_pkt_q.stop;
    upd_pkt.length <= upd_pkt_q.length;
    upd_addr_prev  <= upd_addr;
    case (fsm)
      queue_scan_s : begin
        upd <= 0;
        queue.flushed <= 0;
        // Continiously scan for unacked packets. If present flag found, check if it's acked (queue_check_s)
         // if packet at current address is not present, read next one and so on
        if (queue.flush) fsm <= queue_flush_s; // queue flush request during connection closure
        else if (upd_pkt_q.present) begin // if a packet is present (not yet acknowledged and stored in RAM)
          fsm       <= queue_read_s; // read its pointers and length
          upd_addr  <= upd_addr_prev;
          ack_diff  <= upd_pkt_q.stop - tcb.rem_ack_num; // ack_diff[31] means either ack or expected ack ovfl
          timer     <= upd_pkt_q.timer;
          tries     <= upd_pkt_q.tries;
          start     <= upd_pkt_q.start;
          stop      <= upd_pkt_q.stop;
          free      <= 0;
          retrans   <= 0;
          queue.seq <= upd_pkt_q.start;
	        queue.len <= upd_pkt_q.length;
        end
        else upd_addr <= upd_addr + 1;
      end
      queue_read_s : begin
        fsm <= queue_check_s;
        if (ack_diff[31] || ack_diff == 0) free <= 1; // free packet if stop (expected ack) is less than remote ack
		    else if (!ack_diff[31] && (timer == RETRANSMIT_TICKS)) retrans <= 1; // only transmit if previous packets were sent at least once, and packet is not acked
      end
      queue_check_s : begin
        if (!tx_busy && !load && !load_pend) begin // if TX path isn't busy (e.g. pure ACK) and RAM isn't being loaded with new packet...
          upd <= 1;
          if (free) begin // clear present flag if acked
            fsm <= queue_next_s;
            upd_pkt.present <= 0;
            upd_pkt.timer   <= 0;
            upd_pkt.tries   <= 0;
            queue.pend      <= 0;
          end
          else if (retrans) begin 
            fsm <= queue_retrans_s;
            if (tries == RETRANSMIT_TRIES) queue.force_fin <= 1;
            upd_pkt.present <= 1;
            upd_pkt.timer   <= 0;
            upd_pkt.tries   <= tries + 1;
            queue.pend      <= 1;
          end
          else begin
            fsm <= queue_next_s;
            upd_pkt.present <= 1;
            upd_pkt.tries   <= tries; // increment retransmit timer
            queue.pend      <= 0;
            if (timer != RETRANSMIT_TICKS) upd_pkt.timer <= timer + 1; // prevent overflow
          end
        end
      end
      queue_next_s : begin
        if (free) begin
          free_ptr <= free_ptr + 1;
          ack      <= stop;
        end
        upd           <= 0;
        upd_addr_prev <= upd_addr + 1;
        upd_addr      <= upd_addr + 1;
        fsm           <= queue_wait_s;
      end
      queue_wait_s : begin
        fsm <= queue_scan_s;
      end
      queue_retrans_s : begin
        upd <= 0;
        if (tx_done) begin // Wait for done signal. Can't use !busy due to unkown tx output delay
          fsm        <= queue_scan_s;
          queue.pend <= 0;
          upd_addr   <= upd_addr + 1;
        end
      end
      queue_flush_s : begin
        queue.pend      <= 0;
        upd_addr        <= upd_addr + 1;
        upd_pkt.present <= 0;
        upd             <= 1;
        flush_ctr <= flush_ctr + 1;
        if (flush_ctr == 0 && upd) begin
          queue.flushed <= 1;
        end
      end
      default : begin
        upd             <= 0;
        queue.force_fin <= 1;
        queue.pend      <= 0;
        upd_pkt.present <= 0;
        upd_pkt.timer   <= 0;
        upd_pkt.tries   <= 0;
        fsm             <= queue_scan_s;
      end
    endcase
  end
end

endmodule : tcp_vlg_tx_queue

// Hold raw TCP data to be transmitted, free space when ack received
module tcp_data_queue #(
  parameter D = 16,
  parameter W = 16
)
(
  input  logic         rst,
  input  logic         clk,
  
  input  logic         w_v,
  input  logic [W-1:0] w_d,
  input  logic [31:0]  seq,
  input  logic [31:0]  isn,
  input  logic [31:0]  ack, // free bytes when ack received
  output logic [D-1:0] space_left,
  input  logic [D-1:0] rd_addr, // address to read from 
  output logic [W-1:0] r_q,
  
  output logic         f,
  output logic         e
);

logic [D-1:0] wr_addr;
logic [32:0]  diff;

assign diff = seq - ack;
assign space_left = (diff[D]) ? 0 : ~diff[D-1:0];

assign e = (diff == 0);
assign f = (space_left == 0);

always @ (posedge clk) begin
  if (rst) wr_addr[D-1:0] <= isn[D-1:0];
  else if (w_v) wr_addr <= wr_addr + 1;
end

reg [W-1:0] mem[(1<<D)-1:0];

always @ (posedge clk) r_q <= mem[rd_addr];

always @ (posedge clk) if (w_v) mem[wr_addr] <= w_d;

endmodule : tcp_data_queue
