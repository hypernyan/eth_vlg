import ip_vlg_pkg::*;
import eth_vlg_pkg::*;
import mac_vlg_pkg::*;

module ip_vlg_top #(
  parameter int               N_TCP                = 1,
  parameter            [31:0] MTU                  = 1400,
  parameter [N_TCP-1:0][31:0] TCP_RETRANSMIT_TICKS = 1000000,
  parameter [N_TCP-1:0][31:0] TCP_RETRANSMIT_TRIES = 5,
  parameter [N_TCP-1:0][31:0] TCP_RAM_DEPTH        = 12,        
  parameter [N_TCP-1:0][31:0] TCP_PACKET_DEPTH     = 8,     
  parameter [N_TCP-1:0][31:0] TCP_WAIT_TICKS       = 100,
  parameter mac_addr_t        MAC_ADDR             = 0
)
(
  input logic clk,
  input logic rst,
  mac.in      rx,
  mac.out     tx,
  input dev_t dev,
  input port_t [N_TCP-1:0] port,
  // Connects to ARP table
  output ipv4_t     ipv4_req,
  input  mac_addr_t mac_rsp,
  input  logic      arp_val,
  input  logic      arp_err,
  // Raw UDP
  udp.in  udp_tx,
  udp.out udp_rx,
  // Raw TCP
  input logic    [N_TCP-1:0]  [7:0] tcp_din,
  input logic    [N_TCP-1:0]        tcp_vin,
  output logic   [N_TCP-1:0]        tcp_cts,
  input logic    [N_TCP-1:0]        tcp_snd,

  output logic   [N_TCP-1:0]  [7:0] tcp_dout,
  output logic   [N_TCP-1:0]        tcp_vout,
  // TCP control [N_TCP-1:0]
  input  ipv4_t  [N_TCP-1:0]        rem_ipv4,
  input  port_t  [N_TCP-1:0]        rem_port,
  input  logic   [N_TCP-1:0]        connect, 
  output logic   [N_TCP-1:0]        connected,
  input  logic   [N_TCP-1:0]        listen,
  // DHCP related

  input  logic  dhcp_ipv4_req,  
  input  ipv4_t dhcp_pref_ipv4, 
  output ipv4_t dhcp_ipv4_addr,   
  output logic  dhcp_ipv4_val,    
  output logic  dhcp_ok,     
  output logic  dhcp_timeout
);

ipv4 ipv4_tx(.*);
ipv4 ipv4_rx(.*);
ipv4 icmp_ipv4_tx(.*);
ipv4 udp_ipv4_tx(.*);

ipv4_hdr_t [N_TCP:0] tx_ipv4_hdr_v;
mac_hdr_t  [N_TCP:0] tx_mac_hdr_v;

logic [N_TCP:0] act_ms;
logic rdy, avl;

wor   [N_TCP:0] ind;
logic [N_TCP:0] rst_fifo_vect;

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

udp_vlg udp_vlg_inst (
  .clk    (clk),
  .rst    (rst),
  .rx     (ipv4_rx),
  .tx     (udp_ipv4_tx),
  .udp_tx (udp_tx),
  .udp_rx (udp_rx),
  .dev    (dev)
);

dhcp_vlg #(
  .MAC_ADDR (MAC_ADDR)
) dhcp_vlg_inst (
  .clk (clk),
  .rst (rst),
  .rx  (udp_rx),
  .tx  (udp_tx),
  .dev      (dev),

  .ipv4_req  (dhcp_ipv4_req),
  .pref_ipv4 (dhcp_pref_ipv4),
  .ipv4_addr (dhcp_ipv4_addr),
  .ipv4_val  (dhcp_ipv4_val),
  .ok        (dhcp_ok),
  .timeout   (dhcp_timeout)
);

logic [N_TCP-1:0][7:0] tcp_ipv4_tx_d;
logic [N_TCP-1:0]      tcp_ipv4_tx_v;

genvar i;

generate
  for (i = 0; i < N_TCP; i = i + 1) begin : gen_if
    ipv4 tcp_ipv4_tx(.*);
    ipv4 tcp_ipv4_rx(.*);
  end
endgenerate

generate 
  for (i = 0; i < N_TCP; i = i + 1) begin : gen_tcp
    tcp_vlg #(
      .MAX_PAYLOAD_LEN  (MTU - 120),
      .RETRANSMIT_TICKS (TCP_RETRANSMIT_TICKS[i]),
      .RETRANSMIT_TRIES (TCP_RETRANSMIT_TRIES[i]),
      .RAM_DEPTH        (TCP_RAM_DEPTH[i]),
      .PACKET_DEPTH     (TCP_PACKET_DEPTH[i]),
      .WAIT_TICKS       (TCP_WAIT_TICKS[i])
    ) tcp_vlg_inst (
      .clk (clk),
      .rst (rst),
      .dev (dev),
      .port (port[i]),
      .rx  (gen_if[i].tcp_ipv4_rx),
      .tx  (gen_if[i].tcp_ipv4_tx),
      .din (tcp_din[i]),
      .vin (tcp_vin[i]),
      .cts (tcp_cts[i]),
      .snd (tcp_snd[i]),

      .dout (tcp_dout[i]),
      .vout (tcp_vout[i]),

      .connected (connected[i]),
      .connect   (connect  [i]), 
      .listen    (listen   [i]),  
      .rem_ipv4  (rem_ipv4 [i]),
      .rem_port  (rem_port [i])
    );
    assign gen_if[i].tcp_ipv4_tx.done = ipv4_tx.eof && act_ms[i+1];
    assign gen_if[i].tcp_ipv4_tx.busy = ipv4_tx.busy;

    assign tcp_ipv4_tx_v[i] = gen_if[i].tcp_ipv4_tx.v;
    assign tcp_ipv4_tx_d[i] = gen_if[i].tcp_ipv4_tx.d;

    assign tx_ipv4_hdr_v[i+1] = gen_if[i].tcp_ipv4_tx.ipv4_hdr;
    assign tx_mac_hdr_v [i+1] = gen_if[i].tcp_ipv4_tx.mac_hdr;

    assign gen_if[i].tcp_ipv4_rx.d = ipv4_rx.d;
    assign gen_if[i].tcp_ipv4_rx.v = ipv4_rx.v;
    assign gen_if[i].tcp_ipv4_rx.sof = ipv4_rx.sof;
    assign gen_if[i].tcp_ipv4_rx.eof = ipv4_rx.eof;
    assign gen_if[i].tcp_ipv4_rx.err = ipv4_rx.err;
    assign gen_if[i].tcp_ipv4_rx.payload_length = ipv4_rx.payload_length;
    assign gen_if[i].tcp_ipv4_rx.ipv4_hdr = ipv4_rx.ipv4_hdr;
    assign gen_if[i].tcp_ipv4_rx.mac_hdr = ipv4_rx.mac_hdr;
  end
endgenerate

assign tx_ipv4_hdr_v[0] = icmp_ipv4_tx.ipv4_hdr;
assign tx_mac_hdr_v[0]  = icmp_ipv4_tx.mac_hdr;

generate
  for (i = 0; i < N_TCP + 1; i = i + 1) begin : gen_index
    assign ind = (act_ms[i] == 1'b1) ? i : 0;
    assign rst_fifo_vect[i] = (rst_fifo & act_ms[i]);
  end
endgenerate

assign icmp_ipv4_tx.done = ipv4_tx.eof && act_ms[0];
assign icmp_ipv4_tx.busy = ipv4_tx.busy;

assign ipv4_tx.ipv4_hdr = tx_ipv4_hdr_v[ind]; //
assign ipv4_tx.mac_hdr = tx_mac_hdr_v[ind]; //

buf_mng #(
  .W (8),
  .N (N_TCP + 1),
  .D ({{N_TCP{$clog2(MTU+1)}}, 32'd8}),
  .RWW (1)
)
buf_mng_inst (
  .clk (clk),
  .rst (rst),
  .rst_fifo (rst_fifo_vect), // flush fifo each sent IPv4 packet to avoid sending multiple packet's data if tcp or icmp continue to stream it.

  .v_i ({tcp_ipv4_tx_v[N_TCP-1:0], icmp_ipv4_tx.v}),
  .d_i ({tcp_ipv4_tx_d[N_TCP-1:0], icmp_ipv4_tx.d}),

  .v_o (ipv4_tx.v),
  .d_o (ipv4_tx.d),
  .eof (ipv4_tx.eof),
  .rdy (rdy),      // ipv4_tx is ready to accept data
  .avl (avl),      // data available to ipv4_tx
  .act_ms (act_ms) // tells which header to pass to ipv4_tx
);
endmodule
