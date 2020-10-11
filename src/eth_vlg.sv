import eth_vlg_pkg::*;
import mac_vlg_pkg::*;

module eth_vlg #(
  parameter mac_addr_t        MAC_ADDR             = 'b0,
  parameter ipv4_t            IPV4_ADDR            = 'b0,
  parameter ipv4_t            DEFAULT_GATEWAY      = 'b0,
  parameter bit               DHCP_ENABLE          = 1,
  parameter int               N_TCP                = 1,
  parameter            [31:0] MTU                  = 1400,
  parameter [N_TCP-1:0][31:0] TCP_RETRANSMIT_TICKS = 1000000,
  parameter [N_TCP-1:0][31:0] TCP_RETRANSMIT_TRIES = 5,
  parameter [N_TCP-1:0][31:0] TCP_RAM_DEPTH        = 8,        
  parameter [N_TCP-1:0][31:0] TCP_PACKET_DEPTH     = 2,     
  parameter [N_TCP-1:0][31:0] TCP_WAIT_TICKS       = 1,
  parameter bit               ARP_VERBOSE          = 0
)
(
  phy.in  phy_rx,
  phy.out phy_tx,
  
  input logic clk_rx, // Receive clock from PHY
  input logic clk, // Internal 125 MHz
  input logic rst, // Reset synchronous to clk
  
  udp.in  udp_tx,
  udp.out udp_rx,

  // Raw TCP
  input logic    [N_TCP-1:0] [7:0] tcp_din,
  input logic    [N_TCP-1:0]       tcp_vin,
  output logic   [N_TCP-1:0]       tcp_cts,
  input logic    [N_TCP-1:0]       tcp_snd,

  output logic   [N_TCP-1:0] [7:0] tcp_dout,
  output logic   [N_TCP-1:0]       tcp_vout,
  // TCP control
  input  ipv4_t  [N_TCP-1:0]       rem_ipv4,
  input  port_t  [N_TCP-1:0]       loc_port,
  input  port_t  [N_TCP-1:0]       rem_port,
  input  logic   [N_TCP-1:0]       connect, 
  output logic   [N_TCP-1:0]       connected, 
  input  logic   [N_TCP-1:0]       listen
);

mac mac_rx(.*);
mac mac_tx(.*);
mac mac_arp_tx(.*);
mac mac_ipv4_tx(.*);

dev_t dev;
assign dev.mac_addr  = MAC_ADDR;
assign dev.ipv4_addr = IPV4_ADDR;

logic [1:0] cur, act_ms, rst_fifo_vect;
mac_hdr_t arp_mac_hdr_tx;
mac_addr_t mac_rsp;
ipv4_t ipv4_req;
logic rdy, arp_val, arp_err, rst_fifo_ip, rst_fifo_arp, rst_fifo;

mac_hdr_t [1:0] mac_hdr_v;
assign mac_hdr_v = {mac_ipv4_tx.hdr, mac_arp_tx.hdr};

logic rst_reg = 0;
logic rst_rx = 0;

// Synchronise reset to clk_rx domain
always @ (posedge clk_rx) begin
  rst_reg <= rst;
  rst_rx <= rst_reg;
end

mac_vlg mac_vlg_inst (
  .clk_rx   (clk_rx),
  .rst_rx   (rst_rx),
  .clk      (clk),
  .rst      (rst),
  .rst_fifo (rst_fifo),
  .dev      (dev),
  .phy_rx   (phy_rx),
  .phy_tx   (phy_tx),
  .rx       (mac_rx),
  .tx       (mac_tx)
);

ip_vlg_top #(
	.N_TCP                (N_TCP),
  .MTU                  (MTU),
  .TCP_RETRANSMIT_TICKS (TCP_RETRANSMIT_TICKS),
  .TCP_RETRANSMIT_TRIES (TCP_RETRANSMIT_TRIES),
  .TCP_RAM_DEPTH        (TCP_RAM_DEPTH),        
  .TCP_PACKET_DEPTH     (TCP_PACKET_DEPTH),     
  .TCP_WAIT_TICKS       (TCP_WAIT_TICKS) 
) ip_vlg_top_inst (
  .clk      (clk),
  .rst      (rst),
  
  .dev      (dev),
  .port     (loc_port),
  .ipv4_req (ipv4_req),
  .mac_rsp  (mac_rsp),
  .arp_val  (arp_val),
  .arp_err  (arp_err),
  
  .rx       (mac_rx),
  .tx       (mac_ipv4_tx),
  
  .udp_tx   (udp_tx),
  .udp_rx   (udp_rx),
  
  .tcp_din  (tcp_din),
  .tcp_vin  (tcp_vin),
  .tcp_cts  (tcp_cts),
  .tcp_snd  (tcp_snd),
  
  .tcp_dout (tcp_dout),
  .tcp_vout (tcp_vout),
  
  .connect   (connect), 
  .connected (connected),
  .listen    (listen),
  .rem_ipv4  (rem_ipv4),
  .rem_port  (rem_port)
);

arp_vlg #(
  .VERBOSE (ARP_VERBOSE)
) arp_vlg_inst (
  .clk      (clk),
  .rst      (rst),
  
  .dev      (dev),
  .ipv4_req (ipv4_req),
  .mac_rsp  (mac_rsp),
  .arp_val  (arp_val),
  .arp_err  (arp_err),
  .rx       (mac_rx),
  .tx       (mac_arp_tx)
);

wor ind;
//wire ind;
genvar i;
generate
  for (i = 0; i < 2; i = i + 1) begin : gen
    assign ind = (act_ms[i] == 1'b1) ? i : 0;
  end
endgenerate
always @ (posedge clk) mac_tx.hdr <= mac_hdr_v[ind];

assign rst_fifo_vect = (rst_fifo && act_ms) ? 2'b11 : 2'b00;

buf_mng #(
  .W (8),
  .N (2),
  .D ({32'd8, 32'd8}),
  .RWW (1)
) buf_mng_inst (
  .clk      (clk),
  .rst      (rst),
  .rst_fifo (rst_fifo_vect),
  
  .v_i      ({mac_ipv4_tx.v, mac_arp_tx.v}),
  .d_i      ({mac_ipv4_tx.d, mac_arp_tx.d}),
  
  .v_o      (mac_tx.v),
  .d_o      (mac_tx.d),
  .eof      (),
  .rdy      (mac_tx.rdy),
  .avl      (mac_tx.avl),
  .act_ms   (act_ms)
);

endmodule
