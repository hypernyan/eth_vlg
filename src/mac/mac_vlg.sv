module mac_vlg
  import
    mac_vlg_pkg::*,
    eth_vlg_pkg::*;
 #(
  parameter int    CDC_FIFO_DEPTH = 8,
  parameter int    CDC_DELAY = 4,
  parameter bit    VERBOSE = 1,
  parameter string DUT_STRING = ""
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,
  phy.in      phy_rx,
  phy.out     phy_tx,
  mac.out_rx  rx,
  mac.in_tx   tx
);

  phy phy_rx_sync (.*);
  
  // Syncronyze 125MHz phy_rx_clk
  // to local 125 MHz clock
  // Delay reading for a few ticks
  // in order to avoid packet rip
  // which may be caused by
  // incoherency of rx and local clocks
  
  mac_vlg_cdc #(  
    .FIFO_DEPTH (CDC_FIFO_DEPTH),
    .DELAY      (CDC_DELAY)
  ) mac_vlg_cdc_inst (
    // phy_rx_clk domain
    .clk_in     (phy_rx.clk),      // in
    .rst_in     (phy_rx.rst),      // in
    .data_in    (phy_rx.dat),      // in
    .valid_in   (phy_rx.val),      // in
    .error_in   (phy_rx.err),      // in
    // local clock domain
    .clk_out    (clk),             // in 
    .rst_out    (rst),             // in 
    .data_out   (phy_rx_sync.dat), // out
    .valid_out  (phy_rx_sync.val), // out
    .error_out  (phy_rx_sync.err)  // out
  );
  
  mac_vlg_rx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) mac_vlg_rx_inst (
    .clk      (clk),
    .rst      (rst),
    .dev      (dev),
    .phy      (phy_rx_sync),
    .mac      (rx)
  );
  
  mac_vlg_tx #(
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) mac_vlg_tx_inst (
    .clk      (clk),
    .rst      (rst),
    .dev      (dev),
    .phy      (phy_tx),
    .mac      (tx)
  );

endmodule : mac_vlg
