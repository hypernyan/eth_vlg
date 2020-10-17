import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface udp;
  logic [7:0] dat;
  logic       rdy; // Data ready to UDP
  logic       req; // Data request for tx when done with header
  logic       val;
  logic       sof;
  logic       eof;
  logic       done;
  logic       err;
  logic       broadcast;
  udp_hdr_t   udp_hdr;
  ipv4_hdr_t  ipv4_hdr;
  mac_hdr_t   mac_hdr;
   
  modport in_rx  (input  dat,      val, sof, eof, err, udp_hdr, ipv4_hdr, mac_hdr,            output done);
  modport out_rx (output dat,      val, sof, eof, err, udp_hdr, ipv4_hdr, mac_hdr,            input  done);
  modport in_tx  (input  dat, rdy, val, sof, eof, err, udp_hdr, ipv4_hdr, mac_hdr, broadcast, output done, req);
  modport out_tx (output dat, rdy, val, sof, eof, err, udp_hdr, ipv4_hdr, mac_hdr, broadcast, input  done, req); 
endinterface

module udp_vlg (
  input logic clk,
  input logic rst,
  ipv4.in_rx  rx,
  ipv4.out_tx tx,
  udp.in_tx   udp_tx,
  udp.out_rx  udp_rx,
  input dev_t dev
);

udp_hdr_t hdr;

udp_vlg_rx udp_vlg_rx_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .ipv4 (rx),
  .udp  (udp_rx)
);

udp_vlg_tx udp_vlg_tx_inst (
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

module udp_vlg_rx (
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
    hdr_done  <= 0;
    receiving <= 0;
    err_len   <= 0;
  end
  else begin
    if (udp.sof && (ipv4.ipv4_hdr.proto == UDP)) begin
      $display("UDP ipv4.");  
      udp.mac_hdr  <= ipv4.mac_hdr;
      udp.ipv4_hdr <= ipv4.ipv4_hdr;
      receiving    <= 1;
    end
    if (udp.eof) receiving <= 0;
    hdr[udp_vlg_pkg::UDP_HDR_LEN-1:1] <= hdr[udp_vlg_pkg::UDP_HDR_LEN-2:0];
    if (receiving && byte_cnt == udp_vlg_pkg::UDP_HDR_LEN) hdr_done <= 1;
    if (receiving && ipv4.eof && byte_cnt != ipv4.payload_length) err_len <= !ipv4.eof;
  end
end

assign udp.err = (err_len || ipv4.err);
assign hdr[0] = ipv4.d;

always @ (posedge clk) fsm_rst <= (udp.done || rst || udp.err);

// Output 

always @ (posedge clk) begin
  if (fsm_rst)  begin
    udp.dat  <= 0;
    udp.sof  <= 0;
    udp.eof  <= 0;
    byte_cnt <= 0;
  end
  else begin
    if (ipv4.v && (ipv4.ipv4_hdr.proto == UDP)) byte_cnt <= byte_cnt + 1;
    udp.dat <= ipv4.d;
    udp.sof <= (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN && udp.udp_hdr.dst_port == dev.udp_port);
    udp.eof <= receiving && ipv4.eof;
  end
end
assign udp.val = (hdr_done && receiving && (udp.udp_hdr.dst_port == dev.udp_port));

// Latch header

always @ (posedge clk) begin
  if (fsm_rst) begin
    udp.udp_hdr.src_port <= 0;
    udp.udp_hdr.dst_port <= 0; 
    udp.udp_hdr.length   <= 0; 
    udp.udp_hdr.chsum    <= 0; 
  end
  else begin
    if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-1) begin
      $display("UDP ipv4: src ip: %d:%d:%d:%d. Source port: %d. Target port: %d. ",
        ipv4.ipv4_hdr.src_ip[3], 
        ipv4.ipv4_hdr.src_ip[2],
        ipv4.ipv4_hdr.src_ip[1],
        ipv4.ipv4_hdr.src_ip[0],
        hdr[7:6],
        hdr[5:4]);
      udp.udp_hdr.src_port <= hdr[7:6];
      udp.udp_hdr.dst_port <= hdr[5:4]; 
      udp.udp_hdr.length   <= hdr[3:2]; 
      udp.udp_hdr.chsum    <= hdr[1:0]; 
    end
  end
end

endmodule : udp_vlg_rx

module udp_vlg_tx (
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
    ipv4.v         <= 0;
    transmitting   <= 0;
    byte_cnt       <= 0;
    udp.req        <= 0;
    ipv4.broadcast <= 0;
  end
  else begin
    hdr_tx <= hdr[udp_vlg_pkg::UDP_HDR_LEN-1];
    if (ipv4.v) byte_cnt <= byte_cnt + 1;
    if (udp.rdy && !transmitting) begin
      transmitting <= 1;
      $display("UDP ipv4: sending packet from %d:%d:%d:%d to %d:%d:%d:%d",
          dev.ipv4_addr[3],
          dev.ipv4_addr[2],
          dev.ipv4_addr[1],
          dev.ipv4_addr[0],
          udp.ipv4_hdr.dst_ip[3],
          udp.ipv4_hdr.dst_ip[2],
          udp.ipv4_hdr.dst_ip[1],
          udp.ipv4_hdr.dst_ip[0]
        );
        hdr                  <= udp.udp_hdr;
        ipv4.ipv4_hdr.src_ip <= udp.ipv4_hdr.src_ip; // Assigned at upper handlers
        ipv4.ipv4_hdr.dst_ip <= udp.ipv4_hdr.dst_ip; // Assigned at upper handlers     
        ipv4.ipv4_hdr.id     <= udp.ipv4_hdr.id;
        ipv4.ipv4_hdr.qos    <= udp.ipv4_hdr.qos;
        ipv4.ipv4_hdr.ver    <= 4;
        ipv4.ipv4_hdr.proto  <= ip_vlg_pkg::UDP;
        ipv4.ipv4_hdr.df     <= 0;
        ipv4.ipv4_hdr.mf     <= 0;
        ipv4.ipv4_hdr.ihl    <= 5;
        ipv4.ipv4_hdr.ttl    <= 128;
        ipv4.ipv4_hdr.length <= udp.udp_hdr.length + ip_vlg_pkg::IPV4_HDR_LEN;
        ipv4.ipv4_hdr.fo     <= 0;
        ipv4.broadcast       <= udp.broadcast;
    end
    if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-2) udp.req <= 1; // Done with header, requesting data
    if (transmitting) begin
      hdr[udp_vlg_pkg::UDP_HDR_LEN-1:1] <= hdr[udp_vlg_pkg::UDP_HDR_LEN-2:0];
      ipv4.v <= 1;
    end
    if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-1) hdr_done <= 1;
  end
end

assign udp.done = transmitting && udp.eof;
assign ipv4.sof = transmitting && (byte_cnt == 0);

assign ipv4.eof = udp.done;
assign ipv4.d = (hdr_done) ? udp.dat : hdr_tx;
assign fsm_rst = (rst || udp.done || udp.err);

endmodule

