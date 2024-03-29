module eth_vlg
  import
    eth_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    dns_vlg_pkg::*;
#(
  // General
  parameter mac_addr_t                 MAC_ADDR                  = {8'h42,8'h55,8'h92,8'h16,8'hEE,8'h31}, // Device MAC
  parameter ipv4_t                     DEFAULT_GATEWAY           = {8'd192, 8'd168, 8'd0, 8'hd1},         // Default gateway IP address
  parameter int                        MTU                       = 1400,                                  // Maximum Transmission Unit
  // TCP   
  parameter int                        TCP_RETRANSMIT_TICKS      = 1250000, // 10ms
  parameter int                        TCP_RETRANSMIT_TRIES      = 5,
  parameter int                        TCP_SACK_RETRANSMIT_TICKS = 5,
  parameter int                        TCP_FAST_RETRANSMIT_TICKS = 5,
  parameter int                        TCP_RX_RAM_DEPTH          = 14,        
  parameter int                        TCP_TX_RAM_DEPTH          = 14,        
  parameter int                        TCP_PACKET_DEPTH          = 6,
  parameter int                        TCP_WAIT_TICKS            = 125,       // 1us
  parameter int                        TCP_CONNECTION_TIMEOUT    = 125000000, // 1s
  parameter int                        TCP_ACK_TIMEOUT           = 125000,    // 1ms
  parameter int                        TCP_DUP_ACKS              = 5,
  parameter int                        TCP_FORCE_ACK_PACKETS     = 5,
  parameter int                        TCP_KEEPALIVE_PERIOD      = 600000000, // 5s
  parameter int                        TCP_KEEPALIVE_INTERVAL    = 12500000,  // 5s
  parameter int                        TCP_ENABLE_KEEPALIVE      = 1,
  parameter int                        TCP_KEEPALIVE_TRIES       = 5,
  // DHCP
  parameter int                        DOMAIN_NAME_LEN           = 5,       
  parameter int                        HOSTNAME_LEN              = 8,
  parameter int                        FQDN_LEN                  = 9,
  parameter [DOMAIN_NAME_LEN-1:0][7:0] DOMAIN_NAME               = "fpga0",     // Domain name
  parameter [HOSTNAME_LEN-1:0]   [7:0] HOSTNAME                  = "fpga_eth",  // Hostname
  parameter [FQDN_LEN-1:0]       [7:0] FQDN                      = "fpga_host", // Fully Qualified Domain Name
  parameter int                        REFCLK_HZ                 = 125000000,   // DHCP server reply timeout
  parameter int                        DHCP_DEFAULT_LEASE_SEC    = 600,   // DHCP server reply timeout
  parameter int                        DHCP_TIMEOUT_SEC          = 10,   // DHCP server reply timeout
  parameter int                        DHCP_RETRIES              = 3,           // Synthesyze DHCP (Ignored, always 1)
  parameter bit                        DHCP_ENABLE               = 1,           // Synthesyze DHCP (Ignored, always 1)
  // ARP 
  parameter int                        ARP_TABLE_SIZE            = 8,
  parameter int                        ARP_TIMEOUT_TICKS         = 250000000,
  parameter int                        ARP_TRIES                 = 5,
  // MAC 
  parameter int                        MAC_CDC_FIFO_DEPTH        = 8, 
  parameter int                        MAC_CDC_DELAY             = 3,
  // Simulation 
  parameter bit                        TCP_VERBOSE               = 1,
  parameter bit                        ICMP_VERBOSE              = 1,
  parameter bit                        ARP_VERBOSE               = 1,
  parameter bit                        DHCP_VERBOSE              = 1,
  parameter bit                        UDP_VERBOSE               = 1,
  parameter bit                        IPV4_VERBOSE              = 1,
  parameter bit                        MAC_VERBOSE               = 1,
  parameter string                     DUT_STRING                = ""
)
(
  input logic        clk, // Internal 125 MHz
  input logic        rst, // Reset synchronous to clk
  // Phy interface
  input  logic       phy_rx_clk,
  input  logic       phy_rx_err,
  input  logic       phy_rx_val,
  input  logic [7:0] phy_rx_dat,

  output logic       phy_tx_clk,
  output logic       phy_tx_err,
  output logic       phy_tx_val,
  output logic [7:0] phy_tx_dat,
  // Raw UDP
  input  length_t    udp_len, // data input
  input  logic [7:0] udp_din, // data input
  input  logic       udp_vin, // data valid input
  output logic       udp_cts, // transmission clear to send. user has 1 tick to deassert vin before data is lost

  output logic [7:0] udp_dout, // data output
  output logic       udp_vout, // data output valid
  // UDP control
  input  port_t      udp_loc_port,
  output ipv4_t      udp_ipv4_rx,    
  output port_t      udp_rem_port_rx,
  input  ipv4_t      udp_ipv4_tx,    
  input  port_t      udp_rem_port_tx,
  // Raw TCP
  input  logic [7:0] tcp_din, // data input
  input  logic       tcp_vin, // data valid input
  output logic       tcp_cts, // transmission clear to send. user has 1 tick to deassert vin before data is lost
  input  logic       tcp_snd, // force sending all buffd data not waiting for TCP_WAIT_TICKS

  output logic [7:0] tcp_dout, // data output
  output logic       tcp_vout, // data output valid
  // TCP control
  input  ipv4_t      tcp_rem_ipv4, // remote ipv4 to connect to (valid with 'connect')
  input  port_t      tcp_rem_port, // remote port to connect to (valid with 'connect')
  input  logic       tcp_connect,  // connect to rem_ipv4:rem_port
     
  input  port_t      tcp_loc_port, // local port 
  input  logic       tcp_listen, // listen for incoming connection with any IP and port (valid with 'connect' and 'listen')
  output ipv4_t      tcp_con_ipv4, // remote ipv4 that is currently connected
  output port_t      tcp_con_port, // remote port that is currently connected
  output logic       idle,
  output logic       listening,
  output logic       connecting,
  output logic       connected,
  output logic       disconnecting,
  // Status
  output logic  dhcp_ready, // DHCP successfully assigned IP or failed out to do so
  output logic  dhcp_error, // DHCP error. Not used
  // DHCP related
  input  ipv4_t preferred_ipv4, // local IPv4 to ask from DHCP server or assigned in case of DHCP failure
  input  logic  dhcp_start,     // start DHCP DORA sequence. (i.e. dhcp_start <= !ready)
  output ipv4_t assigned_ipv4,  // assigned IP by DHCP server. Equals to 'preferred_ipv4'
  output logic  dhcp_lease,       // DHCP was unsuccessful
  // DNS related
  input ipv4_t  dns_ipv4_pri, // primary Domain Name Server IPv4 
  input ipv4_t  dns_ipv4_sec, // seconary Domain Name Server IPv4 
  input name_t  dns_name, // requested domain name 
  input logic   dns_start,  // begin query
  output ipv4_t dns_ipv4,   // DNS response of IPv4 
  output logic  dns_ready,  // query ready
  output logic  dns_error   // error during query
);
  
  phy_ifc phy_rx (.*); // gmii input. synchronous to phy_rx.clk. provides optional rst for synchronyzer
  phy_ifc phy_tx (.*); // gmii output synchronous to phy_tx.clk and clk. dat, val, err signals

  mac_ifc      mac_rx(.*);
  mac_ifc      mac_tx(.*);
  mac_ifc      mac_arp_tx(.*);
  mac_ifc      mac_ipv4_tx(.*);
  dhcp_ctl_ifc dhcp_ctl(.*);
  dns_ctl_ifc  dns_ctl(.*);
  udp_data_ifc udp_in(.*);  // user generated raw UDP stream to be transmitted
  udp_data_ifc udp_out(.*); // received raw UDP stream
  udp_ctl_ifc  udp_ctl(.*); // user UDP control
  tcp_ctl_ifc  tcp_ctl(.*);
  tcp_data_ifc tcp_in(.*);
  tcp_data_ifc tcp_out(.*);
  arp_tbl_ifc  arp_tbl(.*);
  dev_t dev;

  logic arp_rst;
  logic connect_gated;
  logic listen_gated; 

  // Unpack interfaces
  // Raw UDP
  assign udp_in.dat = udp_din;
  assign udp_in.val = udp_vin;
  assign udp_cts    = udp_in.cts; 
  
  assign udp_dout   = udp_out.dat;
  assign udp_vout   = udp_out.val;
  // UDP control
  assign udp_ctl.length      = udp_len;
  assign udp_ctl.loc_port    = udp_loc_port;
  assign udp_ipv4_rx         = udp_ctl.ipv4_rx;    
  assign udp_rem_port_rx     = udp_ctl.rem_port_rx;
  assign udp_ctl.ipv4_tx     = udp_ipv4_tx;    
  assign udp_ctl.rem_port_tx = udp_rem_port_tx;
  // Raw TCP
  assign tcp_in.dat = tcp_din;
  assign tcp_in.val = tcp_vin;
  assign tcp_cts    = tcp_in.cts; 
  assign tcp_in.snd = tcp_snd; 
  
  assign tcp_dout   = tcp_out.dat;
  assign tcp_vout   = tcp_out.val;
  // TCP control
  assign tcp_ctl.rem_ipv4 = tcp_rem_ipv4;
  assign tcp_ctl.rem_port = tcp_rem_port;
  assign tcp_ctl.connect  = connect_gated;
  assign tcp_ctl.loc_port = tcp_loc_port;
  assign tcp_ctl.listen   = listen_gated;
  
  assign tcp_con_ipv4 = tcp_ctl.con_ipv4;
  assign tcp_con_port = tcp_ctl.con_port;
  // TCP status
  assign idle             = (tcp_ctl.status == tcp_closed);
  assign listening        = (tcp_ctl.status == tcp_listening);
  assign connecting       = (tcp_ctl.status == tcp_connecting);
  assign connected        = (tcp_ctl.status == tcp_connected);
  assign disconnecting    = (tcp_ctl.status == tcp_disconnecting);
  // DHCP
  assign dhcp_ctl.pref_ip = preferred_ipv4;
  assign dhcp_ctl.start   = dhcp_start;
  assign assigned_ipv4    = dhcp_ctl.assig_ip;
  assign dhcp_lease       = dhcp_ctl.lease;
  assign dhcp_ready       = dhcp_ctl.ready;
  // DNS 
  assign dns_ctl.ipv4_pri = dns_ipv4_pri;
  assign dns_ctl.ipv4_sec = dns_ipv4_sec;
  assign dns_ctl.name     = dns_name;
  assign dns_ipv4         = dns_ctl.ipv4;
  assign dns_ctl.start    = dns_start;
  assign dns_ready        = dns_ctl.ready;
  assign dns_error        = dns_ctl.error;
  // PHY 
  assign phy_rx.clk = phy_rx_clk;
  assign phy_rx.dat = phy_rx_dat;
  assign phy_rx.val = phy_rx_val;

  assign phy_tx_clk = phy_tx.clk;
  assign phy_tx_dat = phy_tx.dat;
  assign phy_tx_val = phy_tx.val;

  /////////
  // MAC //
  /////////

  mac_vlg #(
    .CDC_FIFO_DEPTH (MAC_CDC_FIFO_DEPTH),
    .CDC_DELAY      (MAC_CDC_DELAY),
    .VERBOSE        (MAC_VERBOSE),
    .DUT_STRING     (DUT_STRING)
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

  ipv4_vlg_top #(
    .MTU                       (MTU),
    .TCP_RETRANSMIT_TICKS      (TCP_RETRANSMIT_TICKS),
    .TCP_SACK_RETRANSMIT_TICKS (TCP_SACK_RETRANSMIT_TICKS),
    .TCP_FAST_RETRANSMIT_TICKS (TCP_FAST_RETRANSMIT_TICKS),
    .TCP_RETRANSMIT_TRIES      (TCP_RETRANSMIT_TRIES),
    .TCP_RX_RAM_DEPTH          (TCP_RX_RAM_DEPTH),        
    .TCP_TX_RAM_DEPTH          (TCP_TX_RAM_DEPTH),        
    .TCP_PACKET_DEPTH          (TCP_PACKET_DEPTH),     
    .TCP_WAIT_TICKS            (TCP_WAIT_TICKS),
    .TCP_CONNECTION_TIMEOUT    (TCP_CONNECTION_TIMEOUT),
    .TCP_ACK_TIMEOUT           (TCP_ACK_TIMEOUT),
    .TCP_FORCE_ACK_PACKETS     (TCP_FORCE_ACK_PACKETS),
    .TCP_DUP_ACKS              (TCP_DUP_ACKS),
    .TCP_KEEPALIVE_PERIOD      (TCP_KEEPALIVE_PERIOD),
    .TCP_KEEPALIVE_INTERVAL    (TCP_KEEPALIVE_INTERVAL),
    .TCP_ENABLE_KEEPALIVE      (TCP_ENABLE_KEEPALIVE),
    .TCP_KEEPALIVE_TRIES       (TCP_KEEPALIVE_TRIES),
    .MAC_ADDR                  (MAC_ADDR),
    .DOMAIN_NAME_LEN           (DOMAIN_NAME_LEN),
    .HOSTNAME_LEN              (HOSTNAME_LEN),
    .FQDN_LEN                  (FQDN_LEN),
    .DOMAIN_NAME               (DOMAIN_NAME),
    .HOSTNAME                  (HOSTNAME),
    .FQDN                      (FQDN),
    .REFCLK_HZ                 (REFCLK_HZ),
    .DHCP_TIMEOUT_SEC          (DHCP_TIMEOUT_SEC),
    .DHCP_DEFAULT_LEASE_SEC    (DHCP_DEFAULT_LEASE_SEC),
    .DHCP_ENABLE               (DHCP_ENABLE),
    .IPV4_VERBOSE              (IPV4_VERBOSE),
    .ICMP_VERBOSE              (ICMP_VERBOSE),
    .DHCP_VERBOSE              (DHCP_VERBOSE),
    .UDP_VERBOSE               (UDP_VERBOSE),
    .TCP_VERBOSE               (TCP_VERBOSE),
    .DUT_STRING                (DUT_STRING)
  ) ipv4_vlg_top_inst (
    .clk       (clk),
    .rst       (rst),
    .dev       (dev),
    .rx        (mac_rx),
    .tx        (mac_ipv4_tx),
    .arp_tbl   (arp_tbl),
    .tcp_in    (tcp_in),
    .tcp_out   (tcp_out),
    .tcp_ctl   (tcp_ctl),
    .udp_in    (udp_in),  // user generated raw UDP stream to be transmitted
    .udp_out   (udp_out), // received raw UDP stream
    .udp_ctl   (udp_ctl), // user UDP control
    .dhcp_ctl  (dhcp_ctl),
    .dns_ctl   (dns_ctl)
  );
  
  // IP assignment and TCP control 
  // are available after
  // DHCP success or failure
  
  always_ff @ (posedge clk) begin
    dev.mac_addr  <= MAC_ADDR; // MAC is constant
    if (rst) begin
      dev.ipv4_addr <= 0;
      arp_rst       <= 1;
      connect_gated <= 0;
      listen_gated  <= 0;
    end
    else begin
      connect_gated <= tcp_connect & dhcp_ctl.ready;
      listen_gated  <= tcp_listen  & dhcp_ctl.ready;
    //  dev.ipv4_addr <= (dhcp_ctl.lease) ? dhcp_ctl.assig_ip : dhcp_ctl.pref_ip;
      dev.ipv4_addr <= dhcp_ctl.assig_ip;
      arp_rst <= !dhcp_ctl.ready; // disable ARP until DHCP finishes
    end
  end
  
  arp_vlg #(
    .VERBOSE    (ARP_VERBOSE),
    .TABLE_SIZE (ARP_TABLE_SIZE),
    .DUT_STRING (DUT_STRING),
    .TIMEOUT_TICKS (ARP_TIMEOUT_TICKS),
    .TRIES         (ARP_TRIES)
  ) arp_vlg_inst (
    .clk (clk),
    .rst (arp_rst),
    .dev (dev),
    .tbl (arp_tbl),
    .rx  (mac_rx),
    .tx  (mac_arp_tx)
  );

  eth_vlg_tx_mux #(
    .N (2),
    .W ($bits(mac_meta_t))
  ) eth_vlg_tx_mux_inst (
    .clk  (clk),
    .rst  (rst),
    .meta ({mac_arp_tx.meta, mac_ipv4_tx.meta}),
    .strm ({mac_arp_tx.strm, mac_ipv4_tx.strm}),
    .rdy  ({mac_arp_tx.rdy,  mac_ipv4_tx.rdy }),
    .req  ({mac_arp_tx.req,  mac_ipv4_tx.req }),
    .acc  ({mac_arp_tx.acc,  mac_ipv4_tx.acc }),
    .err  (),
    .done ({mac_arp_tx.done, mac_ipv4_tx.done}),
    
    .meta_mux (mac_tx.meta),
    .strm_mux (mac_tx.strm),
    .rdy_mux  (mac_tx.rdy ),
    .req_mux  (mac_tx.req ),
    .acc_mux  (mac_tx.acc ),
    .err_mux  (),
    .done_mux (mac_tx.done)
  );

endmodule : eth_vlg
