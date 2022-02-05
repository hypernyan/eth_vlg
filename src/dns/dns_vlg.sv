
module dns_vlg 
  import
    eth_vlg_pkg::*,
    dns_vlg_pkg::*,
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*;
#(
  parameter bit    VERBOSE    = 1,
  parameter string DUT_STRING = ""
)
(
  input logic    clk,
  input logic    rst,
  udp_ifc.in_rx  rx,
  udp_ifc.out_tx tx,
  dns_ctl_ifc.in ctl
);

  dns_ifc dns_rx(.*);
  dns_ifc dns_tx(.*);
 
  dns_vlg_core #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) dns_vlg_core_inst (
    .clk  (clk),
    .rst  (rst),
    .rx   (dns_rx),
    .tx   (dns_tx),
    .ctl  (ctl)
  );
 
  dns_vlg_rx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) dns_vlg_rx_inst (
    .clk  (clk),
    .rst  (rst),
    .dns  (dns_rx),
    .udp  (rx)
  );

  dns_vlg_tx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) dns_vlg_tx_inst (
    .clk  (clk),
    .rst  (rst),
    .dns  (dns_tx),
    .udp  (tx)
  );

endmodule : dns_vlg
