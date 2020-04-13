import ip_vlg_pkg::*;
import eth_vlg_pkg::*;
import mac_vlg_pkg::*;

module ip_vlg_top #(
  parameter MTU = 1460
)
(
  input logic clk,
  input logic rst,
  mac.in      rx,
  mac.out     tx,
  input dev_t dev,
  // Connects to ARP table
  output ipv4_t     ipv4_req,
  input  mac_addr_t mac_rsp,
  input  logic      arp_val,
  input  logic      arp_err,
  // Raw UDP
  udp.in  udp_tx,
  udp.out udp_rx,
  // Raw TCP
  input logic [7:0] tcp_din,
  input logic       tcp_vin,
  output logic      tcp_cts,
  output logic [7:0] tcp_dout,
  output logic       tcp_vout,
  // TCP control
  input  ipv4_t      rem_ipv4,
  input  port_t      rem_port,
  input  logic       connect, 
  output logic       connected, 
  input  logic       listen
);

ipv4 ipv4_tx(.*);
ipv4 ipv4_rx(.*);
ipv4 icmp_ipv4_tx(.*);
ipv4 udp_ipv4_tx(.*);
ipv4 tcp_ipv4_tx(.*);

ipv4_hdr_t [1:0] tx_ipv4_hdr_v;
mac_hdr_t  [1:0] tx_mac_hdr_v;

assign tx_ipv4_hdr_v = {tcp_ipv4_tx.ipv4_hdr, icmp_ipv4_tx.ipv4_hdr};
assign tx_mac_hdr_v  = {tcp_ipv4_tx.mac_hdr,  icmp_ipv4_tx.mac_hdr};

logic [1:0] act_ms;
logic rdy, avl, avl_reg;

wor [1:0] ind;
logic [1:0] act_ms_reg, rst_fifo_vect;

ipv4_vlg ipv4_vlg_inst(
  .clk      (clk),
  .rst      (rst),
  .rst_fifo (rst_fifo),

  .mac_rx   (rx),
  .mac_tx   (tx),
  .dev      (dev),

  .rdy      (rdy),
  .avl      (avl),

  .ipv4_req (ipv4_req),
  .mac_rsp  (mac_rsp),
  .arp_val  (arp_val),
  .arp_err  (arp_err),
  .ipv4_tx  (ipv4_tx),
  .ipv4_rx  (ipv4_rx)
);

icmp_vlg icmp_vlg_inst (
  .clk  (clk),
  .rst  (rst),
  .rx   (ipv4_rx),
  .dev  (dev),
  .tx   (icmp_ipv4_tx)
);

tcp_vlg tcp_vlg_inst (
  .clk (clk),
  .rst (rst),
  .dev (dev),
  .rx  (ipv4_rx),
  .tx  (tcp_ipv4_tx),
  .din (tcp_din),
  .vin (tcp_vin),
  .cts (tcp_cts),

  .dout (tcp_dout),
  .vout (tcp_vout),
  
  .connected (connected),
  .connect   (connect), 
  .listen    (listen),  
  .rem_ipv4  (rem_ipv4),
  .rem_port  (rem_port)
);

assign tcp_ipv4_tx.busy  = ipv4_tx.busy;
assign tcp_ipv4_tx.done  = ipv4_tx.eof  && act_ms[1];
assign icmp_ipv4_tx.busy = ipv4_tx.busy;
assign icmp_ipv4_tx.done = ipv4_tx.eof  && act_ms[0];
assign ipv4_tx.ipv4_hdr  = tx_ipv4_hdr_v[ind];
assign ipv4_tx.mac_hdr   = tx_mac_hdr_v[ind];

udp_vlg udp_vlg_inst (
  .clk    (clk),
  .rst    (rst),
  .rx     (ipv4_rx),
  .tx     (udp_ipv4_tx),
  .udp_tx (udp_tx),
  .udp_rx (udp_rx),
  .dev    (dev)
);

genvar i;
generate
  for (i = 0; i < 2; i = i + 1) begin : gen
    assign ind = (act_ms[i] == 1'b1) ? i : 0;
    assign rst_fifo_vect[i] = (rst_fifo & act_ms[i]);
  end
endgenerate

always @ (posedge clk) begin
  act_ms_reg <= act_ms;
  avl_reg <= avl;
end

buf_mng #(
  .W (8),
  .N (2),
  .D ({$clog2(MTU+1), 32'd8}),
  .RWW (1)
)
buf_mng_inst (
  .clk (clk),
  .rst (rst),
  .rst_fifo (rst_fifo_vect), // flush fifo each IPv4 packet to avoid sending multiple packet's data if tcp or icmp continue to stream it.

  .v_i ({tcp_ipv4_tx.v, icmp_ipv4_tx.v}),
  .d_i ({tcp_ipv4_tx.d, icmp_ipv4_tx.d}),

  .v_o (ipv4_tx.v),
  .d_o (ipv4_tx.d),
  .eof (ipv4_tx.eof),
  .rdy (rdy),      // ipv4_tx is ready to accept data
  .avl (avl),      // data available to ipv4_tx
  .act_ms (act_ms) // tells which header to pass to ipv4_tx
);
endmodule
