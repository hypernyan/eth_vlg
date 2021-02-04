import eth_vlg_pkg::*;
import icmp_vlg_pkg::*;
import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;

module icmp_vlg (
  input logic clk,
  input logic rst,
  ipv4.in_rx  rx,
  ipv4.out_tx tx,
  input dev_t dev
);

  icmp icmp(.*);
  
  icmp_vlg_rx icmp_vlg_rx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .ipv4 (rx),
    .icmp (icmp)
  );
  icmp_vlg_tx icmp_vlg_tx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .ipv4 (tx),
    .icmp (icmp)
  );

endmodule : icmp_vlg
