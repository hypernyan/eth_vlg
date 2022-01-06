module ipv4_vlg
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    eth_vlg_pkg::*,
    tcp_vlg_pkg::*;
 #(
  parameter bit    VERBOSE = 1,
  parameter string DUT_STRING = ""

)
(
  input logic     clk,
  input logic     rst,
  mac_ifc.in_rx   mac_rx,
  mac_ifc.out_tx  mac_tx,
  input  dev_t    dev,
  arp_tbl_ifc.out arp_tbl,
  ipv4_ifc.in_tx  tx,
  ipv4_ifc.out_rx rx
);

  ipv4_vlg_rx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) ipv4_vlg_rx_inst (
    .clk  (clk),
    .rst  (rst),
    .mac  (mac_rx),
    .ipv4 (rx),
    .dev  (dev)
  );
  
  ipv4_vlg_tx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) ipv4_vlg_tx_inst (
    .clk      (clk),
    .rst      (rst),
    .mac      (mac_tx),
    .ipv4     (tx),
    .dev      (dev),
    .arp_tbl  (arp_tbl)
  );

endmodule : ipv4_vlg
