import eth_vlg_pkg::*;
import mac_vlg_pkg::*;

module eth_vlg #(
  // General
  parameter mac_addr_t                 MAC_ADDR             = {8'h42,8'h55,8'h92,8'h16,8'hEE,8'h31}, // Device MAC
  parameter ipv4_t                     DEFAULT_GATEWAY      = {8'd192, 8'd168, 8'd0, 8'hd1},         // Default gateway IP address
  parameter            [31:0]          MTU                  = 1400,                                  // Maximum Transmission Unit
  // TCP
  parameter int                        N_TCP                = 1,       // Number of possible simultaneous TCP connections
  parameter [N_TCP-1:0][31:0]          TCP_RETRANSMIT_TICKS = 1000000, // TCP will try to rentransmit a packet after approx. TCP_RETRANSMIT_TICKS*(2**TCP_PACKET_DEPTH)
  parameter [N_TCP-1:0][31:0]          TCP_RETRANSMIT_TRIES = 5,       // Number of retransmission tries before aborting connection
  parameter [N_TCP-1:0][31:0]          TCP_RAM_DEPTH        = 12,      // RAM depth of transmission queue. Amount of bytes may be stored unacked
  parameter [N_TCP-1:0][31:0]          TCP_PACKET_DEPTH     = 8,       // RAM depth of packet information. Amout of generated packets may be stored
  parameter [N_TCP-1:0][31:0]          TCP_WAIT_TICKS       = 100,     // Wait before forming a packet with current data. May be overriden by tcp_snd 
  // DHCP
  parameter int                        DOMAIN_NAME_LEN      = 5,       
  parameter int                        HOSTNAME_LEN         = 8,
  parameter int                        FQDN_LEN             = 9,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME          = "fpga0",     // Domain name
  parameter [0:HOSTNAME_LEN-1]   [7:0] HOSTNAME             = "fpga_eth",  // Hostname
  parameter [0:FQDN_LEN-1]       [7:0] FQDN                 = "fpga_host", // Fully Qualified Domain Name
  parameter int                        DHCP_TIMEOUT         = 125000,      // DHCP server reply timeout
  parameter bit                        DHCP_ENABLE          = 1,           // Synthesyze DHCP (Ignored, always 1)
  // Simulation
  parameter bit                        ARP_VERBOSE          = 1, 
  parameter bit                        DHCP_VERBOSE         = 1,
  parameter bit                        UDP_VERBOSE          = 1,
  parameter bit                        IPV4_VERBOSE         = 1
  
)
(
  
  input logic clk, // Internal 125 MHz
  input logic rst, // Reset synchronous to clk

  phy.in  phy_rx, // gmii input. synchronous to phy_rx.clk. provides optional rst for synchronyzer
  phy.out phy_tx, // gmii output synchronous to phy_tx.clk and clk. dat, val, err signals

  // Raw TCP
  input  logic   [N_TCP-1:0][7:0] tcp_din, // data input
  input  logic   [N_TCP-1:0]      tcp_vin, // data valid input
  output logic   [N_TCP-1:0]      tcp_cts, // transmission clear to send. user has 1 tick to deassert vin before data is lost
  input  logic   [N_TCP-1:0]      tcp_snd, // force sending all queued data not waiting for TCP_WAIT_TICKS

  output logic   [N_TCP-1:0][7:0] tcp_dout, // data output
  output logic   [N_TCP-1:0]      tcp_vout, // data output valid
  
  // TCP control
  input  ipv4_t  [N_TCP-1:0]      rem_ipv4, // remote ipv4 to connect to (valid with 'connect')
  input  port_t  [N_TCP-1:0]      rem_port, // remote port to connect to (valid with 'connect')
  input  logic   [N_TCP-1:0]      connect,  // connect to rem_ipv4:rem_port

  input  port_t  [N_TCP-1:0]      loc_port, // local port 
  input  logic   [N_TCP-1:0]      listen, // listen for incoming connection with any IP and port (valid with 'connect' and 'listen')

  output logic   [N_TCP-1:0]      connected, // connection established (valid with 'connect' and 'listen')
  // Core status
  output logic   ready, // DHCP successfully assigned IP or failed out to do so
  output logic   error, // DHCP error. Not used
  // DHCP related
  input  ipv4_t  preferred_ipv4, // IPv4 to ask from DHCP server or assigned in case of DHCP failure
  input  logic   dhcp_start,     // Start DHCP DORA sequence. (i.e. dhcp_start <= !ready)
  output ipv4_t  assigned_ipv4,  // Assigned IP by DHCP server. Equals to 'preferred_ipv4'
  output logic   dhcp_success,   // DHCP was successful
  output logic   dhcp_fail       // DHCP was unseccessful (tried for )
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
logic [N_TCP-1:0] connect_gated;
logic [N_TCP-1:0] listen_gated; 

mac_vlg mac_vlg_inst (
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

  .connect        (connect_gated), // TCP HS may start only after IP was assigned 
  .listen         (listen_gated),  // TCP HS may start only after IP was assigned 
  .connected      (connected),
  .rem_ipv4       (rem_ipv4),
  .rem_port       (rem_port),

  .ready          (ready),
  .error          (error),
  
  .preferred_ipv4 (preferred_ipv4),
  .dhcp_start     (dhcp_start),
  .assigned_ipv4  (assigned_ipv4),
  .dhcp_success   (dhcp_success),
  .dhcp_fail      (dhcp_fail)
);

// IP assignment and TCP control 
// are available after
// DHCP success or failure
always @ (posedge clk) begin
  if (rst) begin
    dev.ipv4_addr <= 0;
    arp_rst       <= 1;
    connect_gated <= 0;
    listen_gated  <= 0; 
  end
  else begin
    for (int i = 0; i < N_TCP; i++) begin
      connect_gated[i] <= connect[i] & (dhcp_success || dhcp_fail);
      listen_gated[i]  <= listen[i]  & (dhcp_success || dhcp_fail);
    end
    dev.ipv4_addr <= (dhcp_success) ? assigned_ipv4 : (dhcp_fail) ? preferred_ipv4 : 0;
    arp_rst <= !ready; 
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
