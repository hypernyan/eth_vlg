module udp_vlg_top
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int                        MTU                    = 1500,
  parameter mac_addr_t                 MAC_ADDR               = 0,
  parameter [7:0]                      DOMAIN_NAME_LEN        = 5,
  parameter [7:0]                      HOSTNAME_LEN           = 8,
  parameter [7:0]                      FQDN_LEN               = 9,
  parameter [DOMAIN_NAME_LEN-1:0][7:0] DOMAIN_NAME            = "fpga0",
  parameter [HOSTNAME_LEN-1:0]  [7:0]  HOSTNAME               = "fpga_eth",
  parameter [FQDN_LEN-1:0]      [7:0]  FQDN                   = "fpga_host",
  parameter int                        REFCLK_HZ              = 125000000,
  parameter int                        DHCP_DEFAULT_LEASE_SEC = 10,
  parameter int                        DHCP_TIMEOUT_SEC       = 10,
  parameter bit                        DHCP_ENABLE            = 1,
  parameter int                        DHCP_RETRIES           = 3,
  parameter bit                        DHCP_VERBOSE           = 1,
  parameter bit                        UDP_VERBOSE            = 1,
  parameter string                     DUT_STRING             = ""
)
(
  input logic         clk,
  input logic         rst,
  input dev_t         dev,
  ipv4_ifc.in_rx      ipv4_rx,
  ipv4_ifc.out_tx     ipv4_tx,
  udp_data_ifc.in_tx  udp_in,
  udp_data_ifc.out_rx udp_out,
  udp_ctl_ifc.in      udp_ctl,
  dhcp_ctl_ifc.in     dhcp_ctl, // user DHCP control
  dns_ctl_ifc.in      dns_ctl   // user DNS control
);

  udp_ifc udp_tx(.*);
  udp_ifc udp_rx(.*);

  udp_ifc usr_udp_tx(.*);
  udp_ifc dhcp_udp_tx(.*);
  udp_ifc dns_udp_tx(.*);

  logic dhcp_txe;

  // Control User's UDP stream
  
  udp_vlg_tx_ctl #(
    .MTU (MTU)
  ) udp_vlg_tx_ctl_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .data (udp_in),
    .udp  (usr_udp_tx),
    .ctl  (udp_ctl)
  );
  
  assign udp_ctl.ipv4_rx     = udp_rx.meta.ipv4_hdr.src_ip;    
  assign udp_ctl.rem_port_rx = udp_rx.meta.udp_hdr.src_port;

  udp_vlg #(
    .VERBOSE    (UDP_VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) udp_vlg_inst (
    .clk     (clk),
    .rst     (rst),
    .dev     (dev),
    .ipv4_rx (ipv4_rx),
    .ipv4_tx (ipv4_tx),
    .rx      (udp_rx),
    .tx      (udp_tx)
  );

  dhcp_vlg #(
    .MAC_ADDR          (MAC_ADDR),
    .DOMAIN_NAME_LEN   (DOMAIN_NAME_LEN),
    .HOSTNAME_LEN      (HOSTNAME_LEN),
    .FQDN_LEN          (FQDN_LEN),
    .DOMAIN_NAME       (DOMAIN_NAME),
    .HOSTNAME          (HOSTNAME),
    .FQDN              (FQDN),
    .REFCLK_HZ         (REFCLK_HZ),
    .TIMEOUT_SEC       (DHCP_TIMEOUT_SEC),
    .DEFAULT_LEASE_SEC (DHCP_DEFAULT_LEASE_SEC),
    .ENABLE            (DHCP_ENABLE),
    .VERBOSE           (DHCP_VERBOSE),
    .DUT_STRING        (DUT_STRING)
  ) dhcp_vlg_inst (
    .clk (clk),
    .rst (rst),
    .rx  (udp_rx),
    .tx  (dhcp_udp_tx),
    .ctl (dhcp_ctl)
  );
/*
  dns_vlg dns_vlg_inst (
    .clk (clk),
    .rst (rst),
    .rx  (udp_rx),
    .tx  (dns_udp_tx),
    .ctl (dns_ctl)
  );
*/
  eth_vlg_tx_mux #(
    .N (3),
    .W ($bits(udp_meta_t))
  ) eth_vlg_tx_mux_isnt (
    .clk      (clk),
    .rst      (rst),
    .meta     ({dhcp_udp_tx.meta, dns_udp_tx.meta, usr_udp_tx.meta}),
    .strm     ({dhcp_udp_tx.strm, dns_udp_tx.strm, usr_udp_tx.strm}),
    .rdy      ({dhcp_udp_tx.rdy,  dns_udp_tx.rdy,  usr_udp_tx.rdy }),
    .req      ({dhcp_udp_tx.req,  dns_udp_tx.req,  usr_udp_tx.req }),
    .acc      ({dhcp_udp_tx.acc,  dns_udp_tx.acc,  usr_udp_tx.acc }),
    .err      ({dhcp_udp_tx.err,  dns_udp_tx.err,  usr_udp_tx.err }),
    .done     ({dhcp_udp_tx.done, dns_udp_tx.done, usr_udp_tx.done}),
    .meta_mux (udp_tx.meta),
    .strm_mux (udp_tx.strm),
    .rdy_mux  (udp_tx.rdy ),
    .req_mux  (udp_tx.req ),
    .acc_mux  (udp_tx.acc ),
    .err_mux  (udp_tx.err ),
    .done_mux (udp_tx.done)
  );

endmodule : udp_vlg_top
