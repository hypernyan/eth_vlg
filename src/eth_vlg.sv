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
  parameter int                        DHCP_TIMEOUT         = 125000000,   // DHCP server reply timeout
  parameter bit                        DHCP_ENABLE          = 1,           // Synthesyze DHCP (Ignored, always 1)
  // ARP
  parameter int                        ARP_TABLE_SIZE       = 8,
  // MAC
  parameter int                        MAC_TX_FIFO_SIZE     = 8,
  parameter int                        MAC_CDC_FIFO_DEPTH   = 8, 
  parameter int                        MAC_CDC_DELAY        = 3,
  // Simulation
  parameter bit                        TCP_VERBOSE          = 1,
  parameter bit                        ARP_VERBOSE          = 1,
  parameter bit                        DHCP_VERBOSE         = 1,
  parameter bit                        UDP_VERBOSE          = 1,
  parameter bit                        IPV4_VERBOSE         = 1,
  parameter bit                        MAC_VERBOSE          = 1
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
  
  mac_addr_t arp_mac;
  ipv4_t arp_ipv4;
  logic arp_val, arp_err;
  
  logic rst_reg = 0;
  logic rst_rx = 0;
  logic arp_rst;
  logic [N_TCP-1:0] connect_gated;
  logic [N_TCP-1:0] listen_gated; 
  
  /////////
  // MAC //
  /////////
  mac_vlg #(
    .TX_FIFO_SIZE   (MAC_TX_FIFO_SIZE),
    .CDC_FIFO_DEPTH (MAC_CDC_FIFO_DEPTH),
    .CDC_DELAY      (MAC_CDC_DELAY),
    .VERBOSE        (MAC_VERBOSE)
  ) mac_vlg_inst (
    .clk      (clk),
    .rst      (rst),
    .dev      (dev),
    .phy_rx   (phy_rx),
    .phy_tx   (phy_tx),
    .rx       (mac_rx),
    .tx       (mac_tx)
  );
  
  ////////////////////////////
  // IP and upper protocols //
  ////////////////////////////
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
    .IPV4_VERBOSE         (IPV4_VERBOSE),
    .TCP_VERBOSE          (TCP_VERBOSE)
  ) ip_vlg_top_inst (
    .clk            (clk),
    .rst            (rst),
  
    .dev            (dev),
    .port           (loc_port),
    .arp_ipv4       (arp_ipv4),
    .arp_req        (arp_req),
    .arp_mac        (arp_mac),
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
    .VERBOSE    (ARP_VERBOSE),
    .TABLE_SIZE (ARP_TABLE_SIZE)
  ) arp_vlg_inst (
    .clk (clk),
    .rst (arp_rst),
    
    .dev  (dev),
    .ipv4 (arp_ipv4),
    .mac  (arp_mac),
    .req  (arp_req),
    .val  (arp_val),
    .err  (arp_err),
    .rx   (mac_rx),
    .tx   (mac_arp_tx)
  );

  eth_vlg_tx_mux #(
    .N (2), // ARP and IPv4
    .W ($bits(mac_meta_t)) // pass only MAC header as metadata
  ) eth_vlg_tx_mux_inst (
    .clk (clk),
    .rst (rst),
    // UDP, TCP and ICMP interface
    // IPv4 interface
    .dat      ({mac_arp_tx.dat, mac_ipv4_tx.dat}),       
    .val      ({mac_arp_tx.val, mac_ipv4_tx.val}),       
    .sof      ({mac_arp_tx.sof, mac_ipv4_tx.sof}),       
    .eof      ({mac_arp_tx.eof, mac_ipv4_tx.eof}),       
    .rdy      ({mac_arp_tx.rdy, mac_ipv4_tx.rdy}),       
    .req      ({mac_arp_tx.req, mac_ipv4_tx.req}),       
    .meta     ({mac_arp_tx.meta, mac_ipv4_tx.meta}),
    
    .dat_mux  (mac_tx.dat),
    .val_mux  (mac_tx.val),
    .sof_mux  (mac_tx.sof),
    .eof_mux  (mac_tx.eof),
    .rdy_mux  (mac_tx.rdy),
    .req_mux  (mac_tx.req),
    .meta_mux (mac_tx.meta)
  );
endmodule
