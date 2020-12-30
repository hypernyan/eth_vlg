import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface udp;
  logic [7:0] dat;  // data
  logic       val;  // data valid
  logic       sof;  // start of 'dat' frame
  logic       eof;  // stop of 'dat' frame
  logic       err;  // error
  logic       rdy;  // Data ready from to IPv4
  logic       req;  // Data request for tx when done with header
  udp_meta_t  meta;
   
  modport in_rx  (input  dat,      val, sof, eof, err, meta);
  modport out_rx (output dat,      val, sof, eof, err, meta);
  modport in_tx  (input  dat, rdy, val, sof, eof, err, meta, output req);
  modport out_tx (output dat, rdy, val, sof, eof, err, meta, input  req); 
endinterface

module udp_vlg #(
  parameter bit VERBOSE = 1
) (
  input logic clk,
  input logic rst,
  ipv4.in_rx  rx,
  ipv4.out_tx tx,
  udp.in_tx   udp_tx,
  udp.out_rx  udp_rx,
  input dev_t dev
);

udp_hdr_t hdr;

udp_vlg_rx #(
  .VERBOSE (VERBOSE)
) udp_vlg_rx_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .ipv4 (rx),
  .udp  (udp_rx)
);

udp_vlg_tx #(
  .VERBOSE (VERBOSE)
) udp_vlg_tx_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .ipv4 (tx),
  .udp  (udp_tx)
);

endmodule : udp_vlg

import udp_vlg_pkg::*;
import ip_vlg_pkg::*;
import eth_vlg_pkg::*;

module udp_vlg_rx #(
  parameter bit VERBOSE = 1
) (
  input logic clk,
  input logic rst,
  input dev_t dev,
  ipv4.in_rx  ipv4,
  udp.out_rx  udp
);

logic [15:0] byte_cnt;
logic [udp_vlg_pkg::UDP_HDR_LEN-1:0][7:0] hdr;

// Handle incoming packets, check for errors
logic fsm_rst, receiving, hdr_done, err_len;

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr_done     <= 0;
    receiving    <= 0;
    err_len      <= 0;
    hdr[udp_vlg_pkg::UDP_HDR_LEN-1:1] <= 0;
    udp.meta.ipv4_hdr <= 0;
    udp.meta.mac_hdr  <= 0;
  end
  else begin
    if (ipv4.sof && (ipv4.meta.ipv4_hdr.proto == UDP)) begin
      udp.meta.mac_hdr  <= ipv4.meta.mac_hdr;
      udp.meta.ipv4_hdr <= ipv4.meta.ipv4_hdr;
      receiving         <= 1;
    end
    if (ipv4.eof) receiving <= 0;
    hdr[udp_vlg_pkg::UDP_HDR_LEN-1:1] <= hdr[udp_vlg_pkg::UDP_HDR_LEN-2:0];
    if (receiving && byte_cnt == udp_vlg_pkg::UDP_HDR_LEN - 1) hdr_done <= 1;
    if (receiving && ipv4.eof && byte_cnt != ipv4.meta.pl_len) err_len <= !ipv4.eof;
  end
end

assign udp.err = (err_len || ipv4.err);
assign hdr[0] = ipv4.dat;

always @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= (udp.eof || udp.err);

// Output 

always @ (posedge clk) begin
  if (fsm_rst)  begin
    udp.dat  <= 0;
    udp.sof  <= 0;
    udp.eof  <= 0;
    byte_cnt <= 0;
    udp.val  <= 0;
  end
  else begin
    if (ipv4.val && (ipv4.meta.ipv4_hdr.proto == UDP)) byte_cnt <= byte_cnt + 1;
    udp.dat <= ipv4.dat;
    udp.sof <= (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN);
    udp.eof <= receiving && ipv4.eof;
    udp.val <= hdr_done && receiving;
    if (udp.sof && VERBOSE) $display("[DUT]<- UDP rx from %d.%d.%d.%d:%d to %d.%d.%d.%d:%d",
        ipv4.meta.ipv4_hdr.src_ip[3], 
        ipv4.meta.ipv4_hdr.src_ip[2],
        ipv4.meta.ipv4_hdr.src_ip[1],
        ipv4.meta.ipv4_hdr.src_ip[0],
        udp.meta.udp_hdr.src_port,
        dev.ipv4_addr[3], 
        dev.ipv4_addr[2],
        dev.ipv4_addr[1],
        dev.ipv4_addr[0],
        udp.meta.udp_hdr.dst_port
      );
  end
end

// Latch header

always @ (posedge clk) begin
  if (fsm_rst) begin
    udp.meta.udp_hdr.src_port <= 0;
    udp.meta.udp_hdr.dst_port <= 0; 
    udp.meta.udp_hdr.length   <= 0; 
    udp.meta.udp_hdr.chsum    <= 0; 
  end
  else begin
    if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-1) begin
      udp.meta.udp_hdr.src_port <= hdr[7:6];
      udp.meta.udp_hdr.dst_port <= hdr[5:4]; 
      udp.meta.udp_hdr.length   <= hdr[3:2]; 
      udp.meta.udp_hdr.chsum    <= hdr[1:0]; 
    end
  end
end

endmodule : udp_vlg_rx

module udp_vlg_tx #(
  parameter bit VERBOSE = 1
)(
  input logic clk,
  input logic rst,
  input dev_t dev,
  udp.in_tx   udp,
  ipv4.out_tx ipv4
);

logic [udp_vlg_pkg::UDP_HDR_LEN-1:0][7:0] hdr;
logic [7:0] hdr_tx;

logic [15:0] byte_cnt;
logic hdr_done, fsm_rst, transmitting;

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr            <= 0;
    hdr_done       <= 0;
    ipv4.val       <= 0;
    ipv4.rdy       <= 0;
    transmitting   <= 0;
    byte_cnt       <= 0;
    udp.req        <= 0;
    ipv4.meta      <= 0;
  end
  else begin
    hdr_tx <= hdr[udp_vlg_pkg::UDP_HDR_LEN-1];
    if (ipv4.val) byte_cnt <= byte_cnt + 1;
    if (udp.rdy && !transmitting) begin
      ipv4.rdy <= 1;
      hdr                       <= udp.meta.udp_hdr;
      ipv4.meta.pl_len          <= udp.meta.udp_hdr.length;
      ipv4.meta.mac_known       <= udp.meta.mac_known;
      ipv4.meta.mac_hdr.dst_mac <= udp.meta.mac_hdr.dst_mac;
      ipv4.meta.ipv4_hdr.src_ip <= udp.meta.ipv4_hdr.src_ip; // Assigned at upper handlers
      ipv4.meta.ipv4_hdr.dst_ip <= udp.meta.ipv4_hdr.dst_ip; // Assigned at upper handlers     
      ipv4.meta.ipv4_hdr.id     <= udp.meta.ipv4_hdr.id;
      ipv4.meta.ipv4_hdr.qos    <= 0;
      ipv4.meta.ipv4_hdr.ver    <= 4;
      ipv4.meta.ipv4_hdr.proto  <= ip_vlg_pkg::UDP;
      ipv4.meta.ipv4_hdr.df     <= 0;
      ipv4.meta.ipv4_hdr.mf     <= 0;
      ipv4.meta.ipv4_hdr.ihl    <= 5;
      ipv4.meta.ipv4_hdr.ttl    <= 128;
      ipv4.meta.ipv4_hdr.length <= udp.meta.udp_hdr.length + ip_vlg_pkg::IPV4_HDR_LEN;
      ipv4.meta.ipv4_hdr.fo     <= 0;
    //  $display("from udp: length %d", udp.meta.udp_hdr.length + ip_vlg_pkg::IPV4_HDR_LEN);
  //    $display("from udp: pl length %d")
    end
    if (ipv4.req && ipv4.rdy) begin
    if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-2) udp.req <= 1; // Done with header, requesting data
    if (ipv4.req && ipv4.rdy) begin
      if (VERBOSE && !ipv4.val) $display("[DUT]-> UDP tx: sending packet from %d.%d.%d.%d:%d to %d.%d.%d.%d:%d",
          dev.ipv4_addr[3],
          dev.ipv4_addr[2],
          dev.ipv4_addr[1],
          dev.ipv4_addr[0],
          udp.meta.udp_hdr.src_port,
          udp.meta.ipv4_hdr.dst_ip[3],
          udp.meta.ipv4_hdr.dst_ip[2],
          udp.meta.ipv4_hdr.dst_ip[1],
          udp.meta.ipv4_hdr.dst_ip[0],
          udp.meta.udp_hdr.dst_port
        );
      end
      hdr[udp_vlg_pkg::UDP_HDR_LEN-1:1] <= hdr[udp_vlg_pkg::UDP_HDR_LEN-2:0];
      ipv4.val <= 1;
    end
    if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-1) hdr_done <= 1;
  end
end

assign ipv4.sof = ipv4.val && (byte_cnt == 0);

assign ipv4.eof = ipv4.val && udp.eof;
assign ipv4.dat = (hdr_done) ? udp.dat : hdr_tx;
assign fsm_rst = (rst || ipv4.eof || udp.err);

endmodule

