import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

interface ipv4
#( 
	parameter N = 1)
(
);

  logic      [7:0]  d;
  logic             v;
  logic             sof;
  logic             eof;
  logic             err;
  logic             busy;
  logic             done;
  length_t       payload_length;
  ipv4_hdr_t     ipv4_hdr;
  mac_hdr_t      mac_hdr;

  modport in_tx  (input  d, v, sof, eof, err, ipv4_hdr, mac_hdr, payload_length, output busy, done); // used for transmitting ipv4 
  modport out_tx (output d, v, sof, eof, err, ipv4_hdr, mac_hdr, payload_length, input  busy, done); // used for transmitting ipv4 

  modport in_rx  (input  d, v, sof, eof, err, ipv4_hdr, mac_hdr, payload_length); // used for receiving ipv4 
  modport out_rx (output d, v, sof, eof, err, ipv4_hdr, mac_hdr, payload_length); // used for receiving ipv4 
endinterface

module ipv4_vlg (
  input logic clk,
  input logic rst,
  output logic rst_fifo,

  mac.in  mac_rx,
  mac.out mac_tx,
  input  dev_t dev,

  input  logic avl,
  output logic rdy,
// ARP request/response
  output ipv4_t    ipv4_req,
  input mac_addr_t mac_rsp,
  input logic      arp_val,
  input logic      arp_err,

  ipv4.in_tx  ipv4_tx,
  ipv4.out_rx ipv4_rx
);

mac_hdr_t mac_hdr;


ipv4_vlg_rx ipv4_vlg_rx_inst (
  .clk  (clk),
  .rst  (rst),
  .rx   (mac_rx),
  .ipv4 (ipv4_rx),
  .dev  (dev)
);


ipv4_vlg_tx ipv4_vlg_tx_inst (
  .clk  (clk),
  .rst  (rst),
  .rst_fifo (rst_fifo),
  .tx   (mac_tx),
  .ipv4 (ipv4_tx),
  .dev  (dev),
  .avl  (avl),
  .rdy  (rdy),

  .ipv4_req (ipv4_req),
  .mac_rsp  (mac_rsp),
  .arp_val  (arp_val),
  .arp_err  (arp_err)
);

endmodule : ipv4_vlg

module ipv4_vlg_rx (
  input logic clk,
  input logic rst,
  mac.in      rx,
  ipv4.out_rx ipv4,
  input dev_t dev
);

localparam IPV4_HDR_LEN = 20;

// chsum

logic ipv4_v;
logic [7:0] ipv4_d;
logic ipv4_sof;
logic ipv4_eof;

assign ipv4_v = ipv4.v;
assign ipv4_d = ipv4.d;
assign ipv4_sof = ipv4.sof;
assign ipv4_eof = ipv4.eof;

logic [18:0] chsum;
logic [15:0] chsum_rec;
logic [15:0] chsum_calc;
logic [7:0]  chsum_hi;
logic [2:0]  chsum_carry;
logic        chsum_ctrl;
logic        chsum_ok;

assign chsum_carry = chsum[18:16];
assign chsum_calc  = chsum[15:0] + chsum_carry;

logic [15:0] byte_cnt;
logic fsm_rst, receiving, hdr_done;

logic [IPV4_HDR_LEN-1:0][7:0] hdr;

// Handle incoming packets, check for errors
logic [5:0] ihl_bytes;
always @ (posedge clk) begin
  if (fsm_rst || rst) begin
    receiving <= 0;
    hdr_done <= 0;
  //  ipv4.err <= 0;
    chsum <= 0;
    chsum_hi <= 0;
    ipv4.d   <= 0;
    byte_cnt <= 0;
    ipv4.sof <= 0;
    ipv4.eof <= 0;
    ipv4.ipv4_hdr <= 0;
  end
  else begin
    hdr[IPV4_HDR_LEN-1:1] <= hdr[IPV4_HDR_LEN-2:0];
    if (byte_cnt == IPV4_HDR_LEN-2) begin
      ipv4.ipv4_hdr[159:0] <= hdr[19:0];
      ipv4.payload_length <= hdr[17:16] - 20;
    end
    if (rx.sof && (rx.hdr.ethertype == IPv4)) begin
      ihl_bytes <= {rx.d[3:0], 2'b00}; 
      receiving <= 1;
    end
    if (receiving && (byte_cnt == (ihl_bytes - 1))) hdr_done <= 1;
    if (rx.v) begin
      if (byte_cnt[0]) chsum <= chsum + {chsum_hi, rx.d};
      if (!byte_cnt[0]) chsum_hi <= rx.d;
      if (receiving) byte_cnt <= byte_cnt + 1;
    end
    ipv4.d <= rx.d;
    ipv4.sof <= receiving && (byte_cnt == IPV4_HDR_LEN - 1);
    ipv4.eof <= hdr_done && (byte_cnt == ipv4.ipv4_hdr.length - 2);
  end
end

assign ipv4.v   = (hdr_done && (ipv4.ipv4_hdr.dst_ip == dev.ipv4_addr));
assign ipv4.err = rx.err;
assign fsm_rst  = (rx.err || ipv4.eof || ipv4.err);
assign hdr[0] = rx.d;

// Calculate chsum
always @ (posedge clk) begin
  if (fsm_rst) begin
    chsum_ok <= 0;
  end
  else begin
    //if (chsum_ctrl && (chsum_calc == '1)) begin
    if (chsum_ctrl) begin
      chsum_ok <= 1;
    end
    else chsum_ok <= 0;
    if (chsum_ctrl && (chsum_calc != '1)) begin
      //if (fsm == ipv4_payload_s && byte_cnt == ipv4.ipv4_hdr.ihl*4) $display("IPv4 core: Bad header chsum.");
    end
  end
end

endmodule : ipv4_vlg_rx

module ipv4_vlg_tx (
  input  logic  clk,
  input  logic  rst,
  output logic  rst_fifo,
  mac.out       tx,
  ipv4.in_tx    ipv4,
  input  dev_t  dev,
  input  logic  avl,
  output logic  rdy,
  // ARP table request/response
  output ipv4_t   ipv4_req,
  input mac_addr_t mac_rsp,
  input logic      arp_val,
  input logic      arp_err
);

localparam HDR_LEN = 20;

logic [7:0] ipv4_d;
logic ipv4_v;

assign ipv4_d = ipv4.d;
assign ipv4_v = ipv4.v;
logic ipv4_eof;
assign ipv4_eof = ipv4.eof;

logic fsm_rst;
logic hdr_done;

logic [HDR_LEN-1:0][7:0] hdr;
logic [HDR_LEN-1:0][7:0] hdr_calc;
logic [15:0] byte_cnt;


logic [15:0] chsum;
logic [18:0] chsum_carry;
logic [3:0] calc_byte_cnt;
logic calc;
logic calc_done;
logic [7:0] hdr_tx;

assign tx.hdr.src_mac_addr = dev.mac_addr;
assign arp_req_ipv4_addr = ipv4.ipv4_hdr.dst_ip;
assign rst_fifo = fsm_rst;

always @ (posedge clk) begin
  if (fsm_rst) begin
    calc           <= 0;
    hdr_calc       <= 0;
    chsum_carry    <= 0;
    calc_byte_cnt  <= 0;
    hdr_done       <= 0;
    calc_done      <= 0;
    byte_cnt       <= 0;
    rdy            <= 0;
    tx.v           <= 0;
    ipv4_req       <= 0;
    ipv4.busy      <= 0;
  end
  else begin
    if (avl && !ipv4.busy) begin // If data is available, latch the header for that data. !ipv4.busy to latch only once
      ipv4.busy <= 1;
      hdr_calc[19]      <= {ipv4.ipv4_hdr.ver, ipv4.ipv4_hdr.ihl};
      hdr_calc[18]      <= ipv4.ipv4_hdr.qos;
      hdr_calc[17:16]   <= ipv4.ipv4_hdr.length;
      hdr_calc[15:14]   <= ipv4.ipv4_hdr.id;
      hdr_calc[13][7]   <= 0;
      hdr_calc[13][6]   <= ipv4.ipv4_hdr.df;
      hdr_calc[13][5]   <= ipv4.ipv4_hdr.mf;
      hdr_calc[13][4]   <= 0;
      hdr_calc[13][3:0] <= ipv4.ipv4_hdr.fo[11:8];
      hdr_calc[12]      <= ipv4.ipv4_hdr.fo[7:0];
      hdr_calc[11]      <= ipv4.ipv4_hdr.ttl;
      hdr_calc[10]      <= ipv4.ipv4_hdr.proto;
      hdr_calc[9:8]     <= 0;
      hdr_calc[7:4]     <= ipv4.ipv4_hdr.src_ip;
      hdr_calc[3:0]     <= ipv4.ipv4_hdr.dst_ip;
      calc <= 1; // Calculate chsum first
    end
    else if (calc) begin
      ipv4_req <= ipv4.ipv4_hdr.dst_ip; // Request MAC for destination IP
      calc_byte_cnt <= calc_byte_cnt + 1;
      chsum_carry <= chsum_carry + hdr_calc[1:0]; // Shift latched header and add up to chsum and carry
      hdr_calc[HDR_LEN-3:0] <= hdr_calc[HDR_LEN-1:2];
      if (calc_byte_cnt == 10) begin // Done with chsum
        calc_done <= 1; // Ready to readout data
        calc <= 0;
        hdr[19]      <= {ipv4.ipv4_hdr.ver, ipv4.ipv4_hdr.ihl};
        hdr[18]      <= ipv4.ipv4_hdr.qos;
        hdr[17:16]   <= ipv4.ipv4_hdr.length;
        hdr[15:14]   <= ipv4.ipv4_hdr.id;
        hdr[13][7]   <= 0;
        hdr[13][6]   <= ipv4.ipv4_hdr.df;
        hdr[13][5]   <= ipv4.ipv4_hdr.mf;
        hdr[13][4]   <= 0;
        hdr[13][3:0] <= ipv4.ipv4_hdr.fo[11:8];
        hdr[12]      <= ipv4.ipv4_hdr.fo[7:0];
        hdr[11]      <= ipv4.ipv4_hdr.ttl;
        hdr[10]      <= ipv4.ipv4_hdr.proto;
        hdr[9:8]     <= chsum;
        hdr[7:4]     <= ipv4.ipv4_hdr.src_ip;
        hdr[3:0]     <= ipv4.ipv4_hdr.dst_ip;
      end
    end
    if (calc_done && arp_val) begin // done calculating chsum, header completed now. ready to transmit when MAC from ARP table is valid
      tx.hdr.ethertype    <= IPv4;
      tx.hdr.dst_mac_addr <= mac_rsp; // acquire destination MAC from ARP table
      tx.hdr.length       <= ipv4.ipv4_hdr.length + (ipv4.ipv4_hdr.ihl << 2);
      // if (byte_cnt == 0) $display ("<- srv: IPv4 to %d:%d:%d:%d.", hdr[3], hdr[2], hdr[1], hdr[0]);
      hdr[HDR_LEN-1:1] <= hdr[HDR_LEN-2:0];
      byte_cnt <= byte_cnt + 1;
      tx.sof <= (byte_cnt == 0);
      tx.v <= 1;
      if (byte_cnt == HDR_LEN-2) rdy <= 1;    // read out data from buffer. Buffer manager need 2 ticks to start output
      if (byte_cnt == HDR_LEN) hdr_done <= 1; // Done transmitting header, switch to buffer output
    end
  end
end

assign chsum = ~(chsum_carry[18:16] + chsum_carry[15:0]); // Calculate actual chsum
always @ (posedge clk) hdr_tx <= hdr[HDR_LEN-1];

assign tx.d = (hdr_done) ? ipv4.d : hdr_tx; // Switch data output between header and buffer's output
assign fsm_rst = (rst || ipv4.eof || arp_err);
assign tx.eof = ipv4.eof;
logic [7:0] txd;
logic txv;

assign txd = tx.d;
assign txv = tx.v;

endmodule : ipv4_vlg_tx
