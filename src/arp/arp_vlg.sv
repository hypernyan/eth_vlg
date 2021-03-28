module arp_vlg
  import
    arp_vlg_pkg::*,
    mac_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter bit VERBOSE = 1,
  parameter string DUT_STRING = "",
  parameter int TABLE_SIZE = 8
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,
  arp_tbl.in  tbl,
  mac.in_rx   rx,
  mac.out_tx  tx
);

  logic send;
  logic done, send_tx;
  logic [15:0] tx_len;
  arp_hdr_t hdr_rx;
  arp_hdr_t hdr_tx;
  arp_hdr_t hdr_tx_req;

  logic send_reply, send_req;

  arp_vlg_rx #(
    .VERBOSE (VERBOSE),
    .DUT_STRING (DUT_STRING)
  )
  arp_vlg_rx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .hdr  (hdr_rx),
    .mac  (rx),
    .send (send_reply),
    .done (rx_done)
  );

  arp_vlg_tx #(
    .VERBOSE (VERBOSE),
    .DUT_STRING (DUT_STRING)
  )
  arp_vlg_tx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .mac  (tx),
    .hdr  (hdr_tx),
    .send (send_tx),
    .len  (tx_len),
    .done (tx_done),
    .busy (tx_busy)
  );

  // Logic to choose between transmitting request or reply
  always_ff @ (posedge clk) begin
    if (send_reply) begin
      send_tx <= 1;
      hdr_tx.hw_type       <= 1; // ethernet
      hdr_tx.proto         <= hdr_rx.proto;
      hdr_tx.hlen          <= 6;
      hdr_tx.plen          <= hdr_rx.plen;
      hdr_tx.oper          <= 2;
      hdr_tx.src_mac       <= dev.mac_addr;
      hdr_tx.src_ipv4_addr <= dev.ipv4_addr;
      hdr_tx.dst_mac       <= hdr_rx.src_mac;
      hdr_tx.dst_ipv4_addr <= hdr_rx.src_ipv4_addr;
      tx_len <= 72;
    end
    else if (send_req) begin
      send_tx <= 1;
      hdr_tx <= hdr_tx_req;
      tx_len <= 72;
    end
    else send_tx <= 0;
  end

  arp_data arp_data_in (.*);

  arp_vlg_table #(
    .TABLE_SIZE (TABLE_SIZE),
    .VERBOSE    (VERBOSE),
    .DUT_STRING (DUT_STRING)
  ) arp_table_inst (
    .clk      (clk),
    .rst      (rst),
    .arp_in   (arp_data_in),
    .dev      (dev),
    .tbl      (tbl),
    .hdr_tx   (hdr_tx_req),
    .send_req (send_req),
    .tx_busy  (tx_busy)
  );

  // Update ARP entries with data from received IPv4 packets. Ignore broadcast packets
  assign arp_data_in.val       = rx_done;
  assign arp_data_in.mac_addr  = hdr_rx.src_mac;
  assign arp_data_in.ipv4_addr = hdr_rx.src_ipv4_addr;

endmodule : arp_vlg
