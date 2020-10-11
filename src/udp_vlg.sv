import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface udp;
  logic [7:0] d;
  logic       v;
  logic       sof;
  logic       eof;
  logic       send;
  logic       done;
  logic       err;
  udp_hdr_t   udp_hdr;
  ipv4_hdr_t  ipv4_hdr;
  mac_hdr_t   mac_hdr;
  
  modport in  (input  d, v, sof, eof, send, udp_hdr, ipv4_hdr, mac_hdr, err, output done);
  modport out (output d, v, sof, eof, send, udp_hdr, ipv4_hdr, mac_hdr, err, input  done);
endinterface

module udp_vlg (
  input logic clk,
  input logic rst,
  ipv4.in_rx  rx,
  ipv4.out_tx tx,
  udp.in   udp_tx,
  udp.out  udp_rx,
  input dev_t dev
);

udp udp(.*);

udp_hdr_t hdr;

udp_vlg_rx udp_vlg_rx_inst (
  .clk (clk),
  .rst (rst),
  .dev (dev),
  .rx  (rx ),
  .udp (udp_rx)
);

udp_vlg_tx udp_vlg_tx_inst (
  .clk (clk),
  .rst (rst),
  .dev (dev),
  .tx  (tx),
  .udp (udp_tx)
);

endmodule : udp_vlg

import udp_vlg_pkg::*;
import ip_vlg_pkg::*;
import eth_vlg_pkg::*;

module udp_vlg_rx (
  input logic clk,
  input logic rst,
  input dev_t dev,
  ipv4.in_rx     rx,
  udp.out     udp
);

logic [15:0] byte_cnt;
logic [udp_vlg_pkg::HDR_LEN-1:0][7:0] hdr;

// Handle incoming packets, check for errors
logic fsm_rst, receiving, hdr_done, err_len;

always @ (posedge clk) begin
  if (fsm_rst) begin
    udp.send  <= 0;
    hdr_done  <= 0;
    receiving <= 0;
    err_len   <= 0;
  end
  else begin
    if (rx.sof && (rx.ipv4_hdr.proto == UDP)) begin
      $display("UDP RX.");  
      udp.mac_hdr  <= rx.mac_hdr;
      udp.ipv4_hdr <= rx.ipv4_hdr;
      receiving    <= 1;
    end
    if (udp.eof) receiving <= 0;
    hdr[udp_vlg_pkg::HDR_LEN-1:1] <= hdr[udp_vlg_pkg::HDR_LEN-2:0];
    if (receiving && byte_cnt == udp_vlg_pkg::HDR_LEN) hdr_done <= 1;
    if (receiving && rx.eof && byte_cnt != rx.payload_length) err_len <= !rx.eof;
  end
end

assign udp.err = (err_len || rx.err);
assign hdr[0] = rx.d;

always @ (posedge clk) fsm_rst <= (udp.done || rst || udp.err);

// Output 

always @ (posedge clk) begin
  if (fsm_rst)  begin
    udp.d    <= 0;
    udp.sof  <= 0;
    udp.eof  <= 0;
    byte_cnt <= 0;
  end
  else begin
    if (rx.v && (rx.ipv4_hdr.proto == UDP)) byte_cnt <= byte_cnt + 1;
    udp.d <= rx.d;
    udp.sof <= (byte_cnt == udp_vlg_pkg::HDR_LEN && udp.udp_hdr.dst_port == dev.udp_port);
    udp.eof <= receiving && rx.eof;
  end
end
assign udp.v = (hdr_done && receiving && (udp.udp_hdr.dst_port == dev.udp_port));

// Latch header

always @ (posedge clk) begin
  if (fsm_rst) begin
    udp.udp_hdr.src_port <= 0;
    udp.udp_hdr.dst_port <= 0; 
    udp.udp_hdr.length   <= 0; 
    udp.udp_hdr.chsum <= 0; 
  end
  else begin
    if (byte_cnt == udp_vlg_pkg::HDR_LEN-1) begin
      $display("UDP RX: src ip: %d:%d:%d:%d. Source port: %d. Target port: %d. ",
        rx.ipv4_hdr.src_ip[3], 
        rx.ipv4_hdr.src_ip[2],
        rx.ipv4_hdr.src_ip[1],
        rx.ipv4_hdr.src_ip[0],
        hdr[7:6],
        hdr[5:4]);
      udp.udp_hdr.src_port <= hdr[7:6];
      udp.udp_hdr.dst_port <= hdr[5:4]; 
      udp.udp_hdr.length   <= hdr[3:2]; 
      udp.udp_hdr.chsum <= hdr[1:0]; 
    end
  end
end

endmodule : udp_vlg_rx

module udp_vlg_tx (
  input logic clk,
  input logic rst,
  input dev_t dev,
  udp.in      udp,
  ipv4.out_tx tx
);


fifo_sc_if #(8, 8) fifo(.*);
fifo_sc    #(8, 8) fifo_inst(.*);

logic [udp_vlg_pkg::HDR_LEN-1:0][7:0] hdr;
logic [7:0] hdr_tx;

logic [15:0] byte_cnt;
logic hdr_done, fsm_rst, transmitting;

assign fifo.clk = clk;
assign fifo.rst = fsm_rst;
assign fifo.write = udp.v;
assign fifo.data_in = udp.d;

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr <= 0;
    fifo.read <= 0;
    hdr_done <= 0;
    tx.v <= 0;
    transmitting <= 0;
    byte_cnt <= 0;
  end
  else begin
    if (tx.v) byte_cnt <= byte_cnt + 1;
    if (udp.sof) begin
      $display("UDP TX: sending packet from %d:%d:%d:%d to %d:%d:%d:%d",
          dev.ipv4_addr[3],
          dev.ipv4_addr[2],
          dev.ipv4_addr[1],
          dev.ipv4_addr[0],
          udp.ipv4_hdr.dst_ip[3],
          udp.ipv4_hdr.dst_ip[2],
          udp.ipv4_hdr.dst_ip[1],
          udp.ipv4_hdr.dst_ip[0]
        );
        hdr[7:6]             <= dev.udp_port;
        hdr[5:4]             <= udp.udp_hdr.src_port;
        hdr[3:2]             <= udp.udp_hdr.length;
        hdr[1:0]             <= udp.udp_hdr.chsum;
        tx.ipv4_hdr.src_ip   <= dev.ipv4_addr;
        tx.ipv4_hdr.dst_ip   <= udp.ipv4_hdr.src_ip;
        tx.ipv4_hdr.id       <= udp.ipv4_hdr.id;
        tx.ipv4_hdr.qos      <= udp.ipv4_hdr.qos;
        tx.ipv4_hdr.ver      <= 4;
        tx.ipv4_hdr.proto    <= udp.ipv4_hdr.proto;
        tx.ipv4_hdr.df       <= 0;
        tx.ipv4_hdr.mf       <= 0;
        tx.ipv4_hdr.ihl      <= 5;
        tx.ipv4_hdr.ttl      <= 128;
        tx.ipv4_hdr.length   <= udp.ipv4_hdr.length;
        tx.ipv4_hdr.fo       <= 0;
    end
    if (udp.eof) begin
      transmitting <= 1;
    end
    if (byte_cnt == udp_vlg_pkg::HDR_LEN-2) fifo.read <= 1;
    if (transmitting) begin
      hdr[udp_vlg_pkg::HDR_LEN-1:1] <= hdr[udp_vlg_pkg::HDR_LEN-2:0];
      tx.v <= 1;
    end
    if (byte_cnt == udp_vlg_pkg::HDR_LEN-1) hdr_done <= 1;
  end
end

always @ (posedge clk) begin
  hdr_tx <= hdr[udp_vlg_pkg::HDR_LEN-1];
  tx.sof <= fifo.read && !tx.v;
end
 
assign udp.done = transmitting && fifo.empty;
assign tx.eof = udp.done;
assign tx.d = (hdr_done) ? fifo.data_out : hdr_tx;
assign fsm_rst = (rst || udp.done || udp.err);

endmodule

