
module icmp_vlg 
  import
    eth_vlg_pkg::*,
    icmp_vlg_pkg::*,
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*;
#(
  parameter bit    VERBOSE    = 1,
  parameter string DUT_STRING = ""
)
(
  input logic clk,
  input logic rst,
  ipv4.in_rx  rx,
  ipv4.out_tx tx,
  input dev_t dev
);

  icmp icmp(.*);
  
  icmp_vlg_rx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) icmp_vlg_rx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .ipv4 (rx),
    .icmp (icmp)
  );

  icmp_vlg_tx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) icmp_vlg_tx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .ipv4 (tx),
    .icmp (icmp)
  );

endmodule : icmp_vlg
