import eth_vlg_pkg::*;
import mac_vlg_pkg::*;

module eth_vlg #(
  parameter mac_addr_t                 MAC_ADDR             = {8'h42,8'h55,8'h92,8'h16,8'hEE,8'h31}, // MAC ADDRESS
  parameter ipv4_t                     DEFAULT_GATEWAY      = {8'd192, 8'd168, 8'd0, 8'hd1},
  parameter bit                        ARP_VERBOSE          = 1,
  parameter bit                        DHCP_VERBOSE         = 1,
  parameter bit                        UDP_VERBOSE          = 1,
  parameter bit                        IPV4_VERBOSE         = 1,
  parameter int                        N_TCP                = 1,
  parameter            [31:0]          MTU                  = 1400,
  parameter [N_TCP-1:0][31:0]          TCP_RETRANSMIT_TICKS = 1000000,
  parameter [N_TCP-1:0][31:0]          TCP_RETRANSMIT_TRIES = 5,
  parameter [N_TCP-1:0][31:0]          TCP_RAM_DEPTH        = 12,        
  parameter [N_TCP-1:0][31:0]          TCP_PACKET_DEPTH     = 8,     
  parameter [N_TCP-1:0][31:0]          TCP_WAIT_TICKS       = 100,
  parameter int                        DOMAIN_NAME_LEN      = 5,
  parameter int                        HOSTNAME_LEN         = 8,
  parameter int                        FQDN_LEN             = 9,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME          = "fpga0",  
  parameter [0:HOSTNAME_LEN-1]   [7:0] HOSTNAME             = "fpga_eth",  
  parameter [0:FQDN_LEN-1]       [7:0] FQDN                 = "fpga_host",  
  parameter int                        DHCP_TIMEOUT         = 125000,
  parameter bit                        DHCP_ENABLE          = 1,
  parameter int                        DHCP_RETRIES         = 3
)
(
  phy.in  phy_rx,
  phy.out phy_tx,
  
  input logic clk_rx, // Receive clock from PHY
  input logic clk,    // Internal 125 MHz
  input logic rst,    // Reset synchronous to clk

  // Raw TCP
  input  logic   [N_TCP-1:0] [7:0] tcp_din,
  input  logic   [N_TCP-1:0]       tcp_vin,
  output logic   [N_TCP-1:0]       tcp_cts,
  input  logic   [N_TCP-1:0]       tcp_snd,

  output logic   [N_TCP-1:0] [7:0] tcp_dout,
  output logic   [N_TCP-1:0]       tcp_vout,
  // TCP control
  input  ipv4_t  [N_TCP-1:0]       rem_ipv4,
  input  port_t  [N_TCP-1:0]       loc_port,
  input  port_t  [N_TCP-1:0]       rem_port,
  input  logic   [N_TCP-1:0]       connect, 
  output logic   [N_TCP-1:0]       connected, 
  input  logic   [N_TCP-1:0]       listen,
  // Core status
  output logic   ready,
  output logic   error,
  // DHCP related
  input  ipv4_t  preferred_ipv4,
  input  logic   dhcp_start,
  output ipv4_t  assigned_ipv4,
  output logic   dhcp_ipv4_val,
  output logic   dhcp_success,
  output logic   dhcp_timeout
);

mac mac_rx(.*);
mac mac_tx(.*);
mac mac_arp_tx(.*);
mac mac_ipv4_tx(.*);

dev_t dev;
assign dev.mac_addr  = MAC_ADDR; // MAC is constant

logic [1:0] cur, act_ms, rst_fifo_vect;
mac_hdr_t arp_mac_hdr_tx;
mac_addr_t mac_rsp;
ipv4_t ipv4_req;
logic rdy, arp_val, arp_err, rst_fifo_ip, rst_fifo_arp, rst_fifo;

mac_hdr_t [1:0] mac_hdr_v;
assign mac_hdr_v = {mac_ipv4_tx.hdr, mac_arp_tx.hdr};

logic rst_reg = 0;
logic rst_rx = 0;
logic arp_rst;
logic connect_gated;
logic listen_gated; 
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
  .TCP_WAIT_TICKS       (TCP_WAIT_TICKS),
  .MAC_ADDR             (MAC_ADDR),
  .DOMAIN_NAME_LEN      (DOMAIN_NAME_LEN),
  .HOSTNAME_LEN         (HOSTNAME_LEN),
  .FQDN_LEN             (FQDN_LEN),
  .DOMAIN_NAME          (DOMAIN_NAME),
  .HOSTNAME             (HOSTNAME),
  .FQDN                 (FQDN),
  .DHCP_TIMEOUT         (DHCP_TIMEOUT),
  .DHCP_ENABLE          (DHCP_ENABLE),
  .DHCP_RETRIES         (DHCP_RETRIES),
  .DHCP_VERBOSE         (DHCP_VERBOSE),
  .UDP_VERBOSE          (UDP_VERBOSE),
  .IPV4_VERBOSE         (IPV4_VERBOSE)
) ip_vlg_top_inst (
  .clk            (clk),
  .rst            (rst),

  .dev            (dev),
  .port           (loc_port),
  .ipv4_req       (ipv4_req),
  .mac_rsp        (mac_rsp),
  .arp_val        (arp_val),
  .arp_err        (arp_err),

  .rx             (mac_rx),
  .tx             (mac_ipv4_tx),

  .tcp_din        (tcp_din),
  .tcp_vin        (tcp_vin),
  .tcp_cts        (tcp_cts),
  .tcp_snd        (tcp_snd),

  .tcp_dout       (tcp_dout),
  .tcp_vout       (tcp_vout),

  .connect        (connect_gated), // TCP HS may start only when IP is assigned 
  .listen         (listen_gated),  // TCP HS may start only when IP is assigned 
  .connected      (connected),
  .rem_ipv4       (rem_ipv4),
  .rem_port       (rem_port),

  .ready          (ready),
  .error          (error),
  
  .preferred_ipv4 (preferred_ipv4),
  .dhcp_start     (dhcp_start),
  .assigned_ipv4  (assigned_ipv4),
  .dhcp_success   (dhcp_success),
  .dhcp_timeout   (dhcp_timeout)
);


always @ (posedge clk) begin
  if (rst) begin
    dev.ipv4_addr <= 0;
    arp_rst <= 1;
  end
  else begin
    connect_gated <= connect && (dhcp_success || dhcp_timeout);
    listen_gated  <= listen  && (dhcp_success || dhcp_timeout);
    dev.ipv4_addr <= (dhcp_success) ? assigned_ipv4 : (dhcp_timeout) ? preferred_ipv4 : 0;
    arp_rst <= !(dhcp_success || dhcp_timeout); 
  end
end

arp_vlg #(
  .VERBOSE (ARP_VERBOSE)
) arp_vlg_inst (
  .clk      (clk),
  .rst      (arp_rst),
  
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
  
  .v_i      ({mac_ipv4_tx.val, mac_arp_tx.val}),
  .d_i      ({mac_ipv4_tx.dat, mac_arp_tx.dat}),
  
  .v_o      (mac_tx.val),
  .d_o      (mac_tx.dat),
  .eof      (),
  .rdy      (mac_tx.rdy),
  .avl      (mac_tx.avl),
  .act_ms   (act_ms)
);

endmodule
