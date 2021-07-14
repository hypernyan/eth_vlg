module udp_vlg
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter bit    VERBOSE = 1,
  parameter string DUT_STRING = ""
)
(
  input logic clk,
  input logic rst,
  ipv4.in_rx  ipv4_rx,
  ipv4.out_tx ipv4_tx,
  udp.in_tx   tx,
  udp.out_rx  rx,
  input dev_t dev
);
  
  udp_hdr_t hdr;
  
  udp_vlg_rx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) udp_vlg_rx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .ipv4 (ipv4_rx),
    .udp  (rx)
  );
  
  udp_vlg_tx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) udp_vlg_tx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .ipv4 (ipv4_tx),
    .udp  (tx)
  );

endmodule : udp_vlg
