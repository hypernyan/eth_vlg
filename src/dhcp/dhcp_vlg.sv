
module dhcp_vlg 
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*,
    dhcp_vlg_pkg::*;
#(
  parameter mac_addr_t                 MAC_ADDR        = 0,
  parameter [7:0]                      DOMAIN_NAME_LEN = 5,
  parameter [7:0]                      HOSTNAME_LEN    = 8,
  parameter [7:0]                      FQDN_LEN        = 9,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME     = "fpga0",
  parameter [0:HOSTNAME_LEN-1]  [7:0]  HOSTNAME        = "fpga_eth",
  parameter [0:FQDN_LEN-1]      [7:0]  FQDN            = "fpga_host",
  parameter int                        TIMEOUT         = 1250000000,
  parameter bit                        ENABLE          = 1,
  parameter int                        RETRIES         = 3,
  parameter bit                        VERBOSE         = 1,
  parameter string                     DUT_STRING      = ""
)
(
  input logic clk,
  input logic rst,
  udp.out_tx  tx,
  udp.in_rx   rx,
  dhcp_ctl    ctl
);

  dhcp dhcp_rx (.*);
  dhcp dhcp_tx (.*);

  dhcp_vlg_core #(
    .MAC_ADDR        (MAC_ADDR),
    .DOMAIN_NAME_LEN (DOMAIN_NAME_LEN),
    .HOSTNAME_LEN    (HOSTNAME_LEN),
    .FQDN_LEN        (FQDN_LEN),
    .DOMAIN_NAME     (DOMAIN_NAME),
    .HOSTNAME        (HOSTNAME),
    .FQDN            (FQDN),
    .TIMEOUT         (TIMEOUT),
    .ENABLE          (ENABLE),
    .RETRIES         (RETRIES),
    .VERBOSE         (VERBOSE),
    .DUT_STRING      (DUT_STRING)
  ) dhcp_vlg_core_inst (
    .clk (clk),
    .rst (rst),
    .rx  (dhcp_rx),
    .tx  (dhcp_tx),
    .ctl (ctl)
  );

  dhcp_vlg_rx dhcp_vlg_rx_inst (
    .clk  (clk),
    .rst  (rst),
    .dhcp (dhcp_rx),
    .udp  (rx)
  );

  dhcp_vlg_tx #(
    .DOMAIN_NAME     (DOMAIN_NAME),
    .HOSTNAME        (HOSTNAME),
    .FQDN            (FQDN),
    .DOMAIN_NAME_LEN (DOMAIN_NAME_LEN),
    .HOSTNAME_LEN    (HOSTNAME_LEN),
    .FQDN_LEN        (FQDN_LEN)
  ) dhcp_vlg_tx_inst (
    .clk  (clk),
    .rst  (rst),
    .dhcp (dhcp_tx),
    .udp  (tx)
  );

endmodule : dhcp_vlg
