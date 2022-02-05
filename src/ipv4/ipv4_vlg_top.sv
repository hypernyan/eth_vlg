
// IPv4 related protocols
module ipv4_vlg_top 
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    eth_vlg_pkg::*,
    tcp_vlg_pkg::*;
#(
  parameter int                        N_TCP                     = 1,
  parameter int                        MTU                       = 1500,
  parameter int                        TCP_RETRANSMIT_TICKS      = 1000000,
  parameter int                        TCP_RETRANSMIT_TRIES      = 5,
  parameter int                        TCP_SACK_RETRANSMIT_TICKS = 5,
  parameter int                        TCP_FAST_RETRANSMIT_TICKS = 5,
  parameter int                        TCP_RX_RAM_DEPTH          = 12,        
  parameter int                        TCP_TX_RAM_DEPTH          = 12,        
  parameter int                        TCP_PACKET_DEPTH          = 8,     
  parameter int                        TCP_WAIT_TICKS            = 100,
  parameter int                        TCP_CONNECTION_TIMEOUT    = 125000000,
  parameter int                        TCP_ACK_TIMEOUT           = 125000,
  parameter int                        TCP_FORCE_ACK_PACKETS     = 5,
  parameter int                        TCP_DUP_ACKS              = 5,
  parameter int                        TCP_KEEPALIVE_PERIOD      = 600000000,
  parameter int                        TCP_KEEPALIVE_INTERVAL    = 125000000,
  parameter int                        TCP_ENABLE_KEEPALIVE      = 1,
  parameter int                        TCP_KEEPALIVE_TRIES       = 5,
  parameter mac_addr_t                 MAC_ADDR                  = 0,
  parameter int                        DOMAIN_NAME_LEN           = 5,
  parameter int                        HOSTNAME_LEN              = 8,
  parameter int                        FQDN_LEN                  = 9,
  parameter [DOMAIN_NAME_LEN-1:0][7:0] DOMAIN_NAME               = "fpga0",  
  parameter [HOSTNAME_LEN-1:0]   [7:0] HOSTNAME                  = "fpga_eth",  
  parameter [FQDN_LEN-1:0]       [7:0] FQDN                      = "fpga_host",  
  parameter int                        REFCLK_HZ                 = 1250000000,
  parameter int                        DHCP_DEFAULT_LEASE_SEC     = 10,
  parameter int                        DHCP_TIMEOUT_SEC          = 10,
  parameter bit                        DHCP_ENABLE               = 1,
  parameter int                        DHCP_RETRIES              = 3,
  parameter bit                        IPV4_VERBOSE              = 0,
  parameter bit                        ICMP_VERBOSE              = 0,
  parameter bit                        UDP_VERBOSE               = 0,
  parameter bit                        DHCP_VERBOSE              = 0,
  parameter bit                        TCP_VERBOSE               = 0,
  parameter string                     DUT_STRING                = ""
)
(
  input logic         clk,
  input logic         rst,
  input dev_t         dev,
  mac_ifc.in_rx       rx,       // connection from MAC
  mac_ifc.out_tx      tx,       // connection to MAC
  arp_tbl_ifc.out     arp_tbl,  // arp table connection. acquire IPv4 from MAC
  tcp_data_ifc.in_tx  tcp_in,   // user generated raw TCP stream to be transmitted
  tcp_data_ifc.out_rx tcp_out,  // received raw TCP stream
  tcp_ctl_ifc.in      tcp_ctl,  // user TCP control
  udp_data_ifc.in_tx  udp_in,   // user generated raw UDP stream to be transmitted
  udp_data_ifc.out_rx udp_out,  // received raw UDP stream
  udp_ctl_ifc.in      udp_ctl,  // user UDP control
  dhcp_ctl_ifc.in     dhcp_ctl, // user DHCP control
  dns_ctl_ifc.in      dns_ctl   // user DHCP control
);

  ipv4_ifc ipv4_tx(.*);
  ipv4_ifc ipv4_rx(.*);
  
  ipv4_ifc icmp_ipv4_tx(.*);
  ipv4_ifc udp_ipv4_tx(.*);
  ipv4_ifc tcp_ipv4_tx(.*);

  udp_vlg_top #(
    .MTU                    (MTU),
    .MAC_ADDR               (MAC_ADDR),
    .DOMAIN_NAME_LEN        (DOMAIN_NAME_LEN),
    .HOSTNAME_LEN           (HOSTNAME_LEN),
    .FQDN_LEN               (FQDN_LEN),
    .DOMAIN_NAME            (DOMAIN_NAME),
    .HOSTNAME               (HOSTNAME),
    .FQDN                   (FQDN),
    .REFCLK_HZ              (REFCLK_HZ),
    .DHCP_TIMEOUT_SEC       (DHCP_TIMEOUT_SEC),
    .DHCP_DEFAULT_LEASE_SEC (DHCP_DEFAULT_LEASE_SEC),
    .DHCP_ENABLE            (DHCP_ENABLE),
    .DHCP_RETRIES           (DHCP_RETRIES),
    .DHCP_VERBOSE           (DHCP_VERBOSE),
    .UDP_VERBOSE            (UDP_VERBOSE),
    .DUT_STRING             (DUT_STRING)
  ) udp_vlg_top_inst (
    .clk      (clk),
    .rst      (rst),
    .dev      (dev),
    .ipv4_rx  (ipv4_rx),
    .ipv4_tx  (udp_ipv4_tx),
    .udp_in   (udp_in),
    .udp_out  (udp_out),
    .udp_ctl  (udp_ctl),
    .dhcp_ctl (dhcp_ctl), // user DHCP control
    .dns_ctl  (dns_ctl) // user DHCP control
  );
  //////////
  // IPv4 //
  //////////
  ipv4_vlg #(
    .VERBOSE    (IPV4_VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) ipv4_vlg_inst (
    .clk     (clk),
    .rst     (rst),
    .mac_rx  (rx),
    .mac_tx  (tx),
    .dev     (dev),
    .arp_tbl (arp_tbl),
    .tx      (ipv4_tx),
    .rx      (ipv4_rx)
  );
 
  ///////////////
  // ICMP Echo //
  /////////////// 
  icmp_vlg #(
    .VERBOSE    (ICMP_VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) icmp_vlg_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .rx   (ipv4_rx),
    .tx   (icmp_ipv4_tx)
  );

  /////////
  // TCP //
  /////////
  tcp_vlg #(
    .MTU                   (MTU),               
    .RETRANSMIT_TICKS      (TCP_RETRANSMIT_TICKS),  
    .SACK_RETRANSMIT_TICKS (TCP_SACK_RETRANSMIT_TICKS),  
    .FAST_RETRANSMIT_TICKS (TCP_FAST_RETRANSMIT_TICKS),  
    .RETRANSMIT_TRIES      (TCP_RETRANSMIT_TRIES),  
    .RX_RAM_DEPTH          (TCP_RX_RAM_DEPTH),         
    .TX_RAM_DEPTH          (TCP_TX_RAM_DEPTH),         
    .PACKET_DEPTH          (TCP_PACKET_DEPTH),      
    .WAIT_TICKS            (TCP_WAIT_TICKS),        
    .CONNECTION_TIMEOUT    (TCP_CONNECTION_TIMEOUT),
    .ACK_TIMEOUT           (TCP_ACK_TIMEOUT),
    .FORCE_ACK_PACKETS     (TCP_FORCE_ACK_PACKETS),
    .DUP_ACKS              (TCP_DUP_ACKS),
    .KEEPALIVE_PERIOD      (TCP_KEEPALIVE_PERIOD),  
    .KEEPALIVE_INTERVAL    (TCP_KEEPALIVE_INTERVAL),  
    .ENABLE_KEEPALIVE      (TCP_ENABLE_KEEPALIVE),  
    .KEEPALIVE_TRIES       (TCP_KEEPALIVE_TRIES),   
    .VERBOSE               (TCP_VERBOSE),
    .DUT_STRING            (DUT_STRING)
  ) tcp_vlg_inst (
    .clk (clk),
    .rst (rst),
    .dev (dev),
    .rx  (ipv4_rx),
    .tx  (tcp_ipv4_tx),
    .in  (tcp_in),
    .out (tcp_out),
    .ctl (tcp_ctl)
  );

  eth_vlg_tx_mux #(
    .N (3),
    .W ($bits(ipv4_meta_t))
  ) eth_vlg_tx_mux_isnt (
    .clk      (clk),
    .rst      (rst),
    .meta     ({udp_ipv4_tx.meta, tcp_ipv4_tx.meta, icmp_ipv4_tx.meta}),
    .strm     ({udp_ipv4_tx.strm, tcp_ipv4_tx.strm, icmp_ipv4_tx.strm}),
    .rdy      ({udp_ipv4_tx.rdy,  tcp_ipv4_tx.rdy,  icmp_ipv4_tx.rdy}),
    .req      ({udp_ipv4_tx.req,  tcp_ipv4_tx.req,  icmp_ipv4_tx.req}),
    .acc      ({udp_ipv4_tx.acc,  tcp_ipv4_tx.acc,  icmp_ipv4_tx.acc}),
    .err      ({udp_ipv4_tx.err,  tcp_ipv4_tx.err,  icmp_ipv4_tx.err}),
    .done     ({udp_ipv4_tx.done, tcp_ipv4_tx.done, icmp_ipv4_tx.done}),
    .meta_mux (ipv4_tx.meta),
    .strm_mux (ipv4_tx.strm),
    .rdy_mux  (ipv4_tx.rdy),
    .req_mux  (ipv4_tx.req),
    .acc_mux  (ipv4_tx.acc),
    .err_mux  (ipv4_tx.err),
    .done_mux (ipv4_tx.done)
  );

endmodule : ipv4_vlg_top
