import arp_vlg_pkg::*;
import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

interface arp_data ();
  ipv4_t      ipv4_addr;
  mac_addr_t  mac_addr;
  logic       val;
  modport in  (input  ipv4_addr, mac_addr, val);
  modport out (output ipv4_addr, mac_addr, val);
endinterface

module arp_vlg #(
  parameter bit VERBOSE = 1,
  parameter int TABLE_SIZE = 8
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,

  input  ipv4_t     ipv4, // IPv4 address request
  input  logic      req,  // Request valid
  output mac_addr_t mac,  // MAC assigned to ipv4
  output logic      val,  // ARP request successful
  output logic      err,  // ARP error
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
    .VERBOSE (VERBOSE)
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
    .VERBOSE (VERBOSE)
  )
  arp_vlg_tx_inst (
    .clk  (clk),
    .rst  (rst),
    .dev  (dev),
    .mac   (tx),
    .hdr  (hdr_tx),
    .send (send_tx),
    .len  (tx_len),
    .done (tx_done),
    .busy (tx_busy)
  );

  // Logic to choose between transmitting request or reply
  always @ (posedge clk) begin
    if (send_reply) begin
      send_tx <= 1;
      hdr_tx.hw_type       <= 1; // ethernet
      hdr_tx.proto         <= hdr_rx.proto;
      hdr_tx.hlen          <= 6;
      hdr_tx.plen          <= hdr_rx.plen;
      hdr_tx.oper          <= 2;
      hdr_tx.src_mac  <= dev.mac_addr;
      hdr_tx.src_ipv4_addr <= dev.ipv4_addr;
      hdr_tx.dst_mac  <= hdr_rx.src_mac;
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

  arp_table #(
    .TABLE_SIZE (TABLE_SIZE),
    .VERBOSE    (VERBOSE)
  ) arp_table_inst (
    .clk      (clk),
    .rst      (rst),
  
    .arp_in   (arp_data_in),
    .dev      (dev),
  
    .ipv4     (ipv4),
    .req      (req),
    .mac      (mac),
    .val      (val),
    .err      (err),
  
    .hdr_tx   (hdr_tx_req),
    .send_req (send_req),
    .tx_busy  (tx_busy)
  );

  // Update ARP entries with data from received IPv4 packets. Ignore broadcast packets
  assign arp_data_in.val       = rx_done;
  assign arp_data_in.mac_addr  = hdr_rx.src_mac;
  assign arp_data_in.ipv4_addr = hdr_rx.src_ipv4_addr;

endmodule : arp_vlg

module arp_vlg_rx #(
  parameter VERBOSE = 1
)
(
  input  logic     clk,
  input  logic     rst,

  input  dev_t     dev,
  output arp_hdr_t hdr,
  mac.in_rx        mac,
  output logic     send,
  output logic     done
);

  localparam [5:0] LEN = 45;
  localparam [4:0] ARP_LEN = 27;
  
  logic [7:0] rx_d;
  logic       rx_v;
  
  assign rx_d = mac.dat;
  assign rx_v = mac.val;
  
  logic [ARP_LEN-1:0][7:0] cur_hdr;
  logic [5:0] byte_cnt;
  logic fsm_rst;
  logic err;
  assign err = (mac.val && byte_cnt == LEN+1);
  assign fsm_rst = (done || rst || err || mac.err);
  
  assign cur_hdr[0] = mac.dat;
  
  always @ (posedge clk) begin
    if (fsm_rst) begin
      cur_hdr[ARP_LEN-1:1] <= 0;
      done <= 0;
      byte_cnt <= 0;
    end
    else if (mac.val && mac.meta.hdr.ethertype == 16'h0806) begin
      cur_hdr[ARP_LEN-1:1] <= cur_hdr[ARP_LEN-2:0];
      byte_cnt <= byte_cnt + 1;
      if (byte_cnt == ARP_LEN) hdr <= cur_hdr;
      if (byte_cnt == LEN) done <= 1;
    end
  end
  
  assign send = (done && !mac.val && hdr.dst_ipv4_addr == dev.ipv4_addr && hdr.oper == 1);
  
  always @ (posedge clk) begin
    if (done && !mac.val && VERBOSE) begin
      $display("->%d.%d.%d.%d: ARP request from %d.%d.%d.%d at %h:%h:%h:%h:%h:%h to %d.%d.%d.%d at %h:%h:%h:%h:%h:%h",
        dev.ipv4_addr[3],
        dev.ipv4_addr[2],
        dev.ipv4_addr[1],
        dev.ipv4_addr[0],
        hdr.src_ipv4_addr[3],
        hdr.src_ipv4_addr[2],
        hdr.src_ipv4_addr[1],
        hdr.src_ipv4_addr[0],
        hdr.src_mac[5],
        hdr.src_mac[4],
        hdr.src_mac[3],
        hdr.src_mac[2],
        hdr.src_mac[1],
        hdr.src_mac[0],
        hdr.dst_ipv4_addr[3],
        hdr.dst_ipv4_addr[2],
        hdr.dst_ipv4_addr[1],
        hdr.dst_ipv4_addr[0],
        hdr.dst_mac[5],
        hdr.dst_mac[4],
        hdr.dst_mac[3],
        hdr.dst_mac[2],
        hdr.dst_mac[1],
        hdr.dst_mac[0]
      );
    end
  end

endmodule : arp_vlg_rx

module arp_vlg_tx #(
  parameter bit VERBOSE = 1
)
(
  input  logic clk,
  input  logic rst,

  input  dev_t        dev,
  mac.out_tx          mac,
  input  arp_hdr_t    hdr,
  input  logic        send,
  input  logic [15:0] len,
  output logic        done,
  output logic        busy
);

  localparam [5:0] LEN = 46;
  
  logic [arp_vlg_pkg::ARP_HDR_LEN-1:0][7:0] data;
  logic [5:0] byte_cnt;
  logic fsm_rst;

  enum logic [3:0] {
    arp_idle_s,
    arp_wait_s,
    arp_delay_s,
    arp_tx_s
  } fsm;

  always @ (posedge clk) begin
    if (fsm_rst) begin
      fsm      <= arp_idle_s;
      byte_cnt <= 0;
      mac.val  <= 0;
      done     <= 0;
      busy     <= 0;
      mac.sof  <= 0;
      mac.eof  <= 0;
      data     <= 0;
      mac.meta <= 0;
      mac.rdy  <= 0;
    end
    else begin
      case (fsm)
        arp_idle_s : begin
          if (send) begin
            fsm  <= arp_wait_s;
            busy <= 1;
            mac.meta.hdr.dst_mac   <= hdr.dst_mac;
            mac.meta.hdr.ethertype <= eth_vlg_pkg::ARP;
            mac.meta.hdr.src_mac   <= dev.mac_addr;
            mac.meta.len           <= LEN;
            if (VERBOSE) begin
              if (hdr.oper == 1) $display("<-%d.%d.%d.%d: *ARP* Who has %d.%d.%d.%d?",
                dev.ipv4_addr[3],
                dev.ipv4_addr[2],
                dev.ipv4_addr[1],
                dev.ipv4_addr[0],
                hdr.dst_ipv4_addr[3],
                hdr.dst_ipv4_addr[2],
                hdr.dst_ipv4_addr[1],
                hdr.dst_ipv4_addr[0]
              );
              if (hdr.oper == 2) $display("<-%d.%d.%d.%d: *ARP* %d.%d.%d.%d is at %h:%h:%h:%h:%h:%h",
                dev.ipv4_addr[3],
                dev.ipv4_addr[2],
                dev.ipv4_addr[1],
                dev.ipv4_addr[0],
                hdr.src_ipv4_addr[3],
                hdr.src_ipv4_addr[2],
                hdr.src_ipv4_addr[1],
                hdr.src_ipv4_addr[0],
                hdr.dst_mac[5],
                hdr.dst_mac[4],
                hdr.dst_mac[3],
                hdr.dst_mac[2],
                hdr.dst_mac[1],
                hdr.dst_mac[0]
              );
            end
          end
          data <= {
            16'd1,
            hdr.proto,
            8'd6,
            8'd4,
            hdr.oper,
            dev.mac_addr,
            dev.ipv4_addr,
            hdr.dst_mac,
            hdr.dst_ipv4_addr
          };
        end
        arp_wait_s : begin
          mac.rdy <= 1;
          if (mac.req) begin
            fsm <= arp_delay_s;
          end
        end
        arp_delay_s : begin
          fsm <= arp_tx_s;
          mac.sof <= 1;
          mac.val <= 1;
        end
        arp_tx_s : begin
          mac.sof <= 0;
          byte_cnt <= byte_cnt + 1;
          data[arp_vlg_pkg::ARP_HDR_LEN-1:1] <= data[arp_vlg_pkg::ARP_HDR_LEN-2:0];
          if (byte_cnt == LEN-3) done <= 1;
          mac.eof <= done;
        end
      endcase
    end
  end
  
  always @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= done;
  
  assign mac.dat = data[arp_vlg_pkg::ARP_HDR_LEN-1];

endmodule : arp_vlg_tx

// Handle data storage and logic requests 
// to acquire destination MAC
module arp_table #(
  parameter int TABLE_SIZE = 2,
  parameter int ARP_TIMEOUT_TICKS = 1000000,
  parameter bit VERBOSE = 1
)
(
  input logic       clk,
  input logic       rst,

  input dev_t       dev,    // local device info
  arp_data.in       arp_in, // interface to load new entries

  output arp_hdr_t  hdr_tx, // 
  output logic      send_req,
  input  logic      tx_busy,

  input  ipv4_t     ipv4,
  input  logic      req,
  output mac_addr_t mac,
  output logic      val,
  output logic      err
);

  logic [TABLE_SIZE-1:0] w_ptr;
  logic [TABLE_SIZE-1:0] arp_table_a_a_prev;
  logic [TABLE_SIZE-1:0] arp_table_a_b_prev;
  
  ipv4_t     cur_ipv4_addr;
  mac_addr_t cur_mac_addr;
  
  ipv4_t ipv4_addr_d_a;
  mac_addr_t mac_addr_d_a;
  ipv4_t ipv4_addr_q_a;
  mac_addr_t mac_addr_q_a;
  
  ipv4_t ipv4_addr_d_b;
  mac_addr_t mac_addr_d_b;
  ipv4_t ipv4_addr_q_b;
  mac_addr_t mac_addr_q_b;
  
  localparam MAC_ADDR_LEN = 48;
  localparam IPV4_ADDR_LEN = 32;
  
  ram_if_dp #(TABLE_SIZE, 80) arp_table(.*); // IPv4 bits = 32, MAC bits = 48;
  ram_dp #(TABLE_SIZE, 80) arp_table_inst (.mem_if (arp_table)); // IPv4 bits = 32, MAC bits = 48;
  assign arp_table.clk_a = clk;
  assign arp_table.clk_b = clk;
  
  assign arp_table.d_a = {cur_ipv4_addr, cur_mac_addr}; // Always rewrite entries from fifo
  assign arp_table.d_b = {ipv4_addr_d_b, mac_addr_d_b};
  
  assign ipv4_addr_d_b = 0;
  assign mac_addr_d_b  = 0;

  assign {ipv4_addr_q_a, mac_addr_q_a} = arp_table.q_a;
  assign {ipv4_addr_q_b, mac_addr_q_b} = arp_table.q_b;
  
  logic [$clog2(ARP_TIMEOUT_TICKS+1)-1:0] arp_timeout_ctr;
  // Add and update logic
  enum logic [3:0] {
      w_idle_s,
      w_scan_s,
      w_upd_s,
      w_add_s
  } w_fsm;
  
  always @ (posedge clk) begin
    if (rst) begin
      w_fsm <= w_idle_s;
      w_ptr <= 0;
      arp_table.a_a <= 0;
      arp_table.w_a <= 0;
    end
    else begin
      case (w_fsm)
          w_idle_s : begin
            arp_table.w_a <= 0;
            arp_table.a_a <= 0;
            arp_table_a_a_prev <= 0;
            if (arp_in.val) begin // When new entry arrives to table
              cur_ipv4_addr <= arp_in.ipv4_addr;
              cur_mac_addr  <= arp_in.mac_addr;
              w_fsm <= w_scan_s;
            end
         //   if (!fifo.empty) begin // Received new ARP packet
         //     fifo.read <= 1;
         //   end
         //   if (fifo.read) begin // Delay by 1
         //     w_fsm <= w_scan_s;
         //     fifo.read <= 0;
         //   end
          end
          w_scan_s : begin
            arp_table.a_a <= arp_table.a_a + 1; // Scanning table...
            arp_table_a_a_prev <= arp_table.a_a;
            if (cur_ipv4_addr == ipv4_addr_q_a) begin
              w_fsm <= w_upd_s;
              if (VERBOSE) $display("%d.%d.%d.%d: ARP entry for %d:%d:%d:%d. Old:%h:%h:%h:%h:%h:%h. New:%h:%h:%h:%h:%h:%h.",
                dev.ipv4_addr[3],
                dev.ipv4_addr[2],
                dev.ipv4_addr[1],
                dev.ipv4_addr[0],
                cur_ipv4_addr[3],
                cur_ipv4_addr[2],
                cur_ipv4_addr[1],
                cur_ipv4_addr[0],
                mac_addr_q_a[5],
                mac_addr_q_a[4],
                mac_addr_q_a[3],
                mac_addr_q_a[2],
                mac_addr_q_a[1],
                mac_addr_q_a[0],
                cur_mac_addr[5],
                cur_mac_addr[4],
                cur_mac_addr[3],
                cur_mac_addr[2],
                cur_mac_addr[1],
                cur_mac_addr[0]
              );
            end
            else if (arp_table.a_a == 0 && arp_table_a_a_prev == '1) begin // Table scanned, counter overflow
              w_fsm <= w_add_s;
              arp_table.a_a <= w_ptr;
              if (VERBOSE) $display("%d.%d.%d.%d: No ARP entry found for %d:%d:%d:%d. Set at %h:%h:%h:%h:%h:%h.",
                dev.ipv4_addr[3],
                dev.ipv4_addr[2],
                dev.ipv4_addr[1],
                dev.ipv4_addr[0],
                cur_ipv4_addr[3],
                cur_ipv4_addr[2],
                cur_ipv4_addr[1],
                cur_ipv4_addr[0],
                cur_mac_addr[5],
                cur_mac_addr[4],
                cur_mac_addr[3],
                cur_mac_addr[2],
                cur_mac_addr[1],
                cur_mac_addr[0]
              );
            end
          end
          w_add_s : begin
            w_ptr <= w_ptr + 1; // Increment current write pointer
            arp_table.a_a <= w_ptr;
            arp_table.w_a <= 1;
            w_fsm <= w_idle_s;
          end
          w_upd_s : begin
            arp_table.a_a <= arp_table_a_a_prev;
            arp_table.w_a <= 1;
            w_fsm <= w_idle_s;
          end
      endcase
    end
  end
  
  enum logic [2:0] {
      r_idle_s,
      r_scan_s,
      r_busy_s,
      r_wait_s
  } r_fsm;
  
  ipv4_t ipv4_reg;
  logic [TABLE_SIZE:0] scan_ctr;
  
  // Scan/request ARP and readout logic
  always @ (posedge clk) begin
    if (rst) begin
      ipv4_reg        <= '0;
      arp_table.a_b   <= 0;
      arp_table.w_b   <= 0;
      r_fsm           <= r_idle_s;
      val             <= 0;
      arp_timeout_ctr <= 0;
      send_req        <= 0;
      err             <= 0;
      scan_ctr        <= 0;
    end
    else begin
      case (r_fsm)
        r_idle_s : begin
          arp_timeout_ctr <= 0;
          err             <= 0;
          arp_table.a_b   <= 0;
          ipv4_reg        <= ipv4;
          scan_ctr        <= 0;
          if (req) begin
            val <= 0;
            r_fsm <= r_scan_s;
            if (VERBOSE) $display("%d.%d.%d.%d: Requesting MAC for %d:%d:%d:%d.",
              dev.ipv4_addr[3],
              dev.ipv4_addr[2],
              dev.ipv4_addr[1],
              dev.ipv4_addr[0],
              ipv4[3],
              ipv4[2],
              ipv4[1],
              ipv4[0]
            );
          end
        end
        r_scan_s : begin
          scan_ctr <= scan_ctr + 1;
          arp_table.a_b <= arp_table.a_b + 1;
          arp_table_a_b_prev <= arp_table.a_b;
          if (ipv4_addr_q_b == ipv4) begin
            mac <= mac_addr_q_b;
            val <= 1;
            r_fsm <= r_idle_s;
            if (VERBOSE) $display("%d.%d.%d.%d: ARP table request complete: found entry for %d:%d:%d:%d at %h:%h:%h:%h:%h:%h.",
              dev.ipv4_addr[3],
              dev.ipv4_addr[2],
              dev.ipv4_addr[1],
              dev.ipv4_addr[0],
              ipv4_reg[3],
              ipv4_reg[2],
              ipv4_reg[1],
              ipv4_reg[0],
              mac_addr_q_b[5],
              mac_addr_q_b[4],
              mac_addr_q_b[3],
              mac_addr_q_b[2],
              mac_addr_q_b[1],
              mac_addr_q_b[0]
            );
          end
          else if (scan_ctr[TABLE_SIZE]) begin // Counter overlow. Entry not found. ARP request
            hdr_tx.hw_type       <= 1;
            hdr_tx.proto         <= 16'h0800; // ipv4
            hdr_tx.hlen          <= 6;
            hdr_tx.plen          <= 4;
            hdr_tx.oper          <= 1;
            hdr_tx.src_mac  <= dev.mac_addr;
            hdr_tx.src_ipv4_addr <= dev.ipv4_addr;
            hdr_tx.dst_mac  <= 48'hffffffffffff;
            hdr_tx.dst_ipv4_addr <= ipv4_reg;
            r_fsm <= r_busy_s; // request MAC
            if (VERBOSE) $display("%d.%d.%d.%d: No ARP entry found for %d:%d:%d:%d. Requesting...",
              dev.ipv4_addr[3],
              dev.ipv4_addr[2],
              dev.ipv4_addr[1],
              dev.ipv4_addr[0],
              ipv4_reg[3],
              ipv4_reg[2],
              ipv4_reg[1],
              ipv4_reg[0]
            );
          end
        end
        r_busy_s : begin
          if (!tx_busy) begin
            r_fsm <= r_wait_s;
            send_req <= 1;
          end
          else send_req <= 0;
        end
        r_wait_s : begin
          send_req <= 0;
          arp_timeout_ctr <= arp_timeout_ctr + 1;
          if (arp_in.val && arp_in.ipv4_addr == ipv4_reg) begin
            mac <= arp_in.mac_addr;
            val <= 1;
            r_fsm <= r_idle_s;
            if (VERBOSE) $display("%d.%d.%d.%d: Received ARP reply for %d:%d:%d:%d at %h:%h:%h:%h:%h:%h.",
              dev.ipv4_addr[3],
              dev.ipv4_addr[2],
              dev.ipv4_addr[1],
              dev.ipv4_addr[0],
              ipv4_reg[3],
              ipv4_reg[2],
              ipv4_reg[1],
              ipv4_reg[0],
              arp_in.mac_addr[5],
              arp_in.mac_addr[4],
              arp_in.mac_addr[3],
              arp_in.mac_addr[2],
              arp_in.mac_addr[1],
              arp_in.mac_addr[0]
            );
          end
          else if (arp_timeout_ctr == ARP_TIMEOUT_TICKS) begin
            err <= 1;
            r_fsm <= r_idle_s;
            if (VERBOSE) $display("%d.%d.%d.%d: No ARP reply for %d:%d:%d:%d.",
              dev.ipv4_addr[3],
              dev.ipv4_addr[2],
              dev.ipv4_addr[1],
              dev.ipv4_addr[0],
              ipv4_reg[3],
              ipv4_reg[2],
              ipv4_reg[1],
              ipv4_reg[0]
            );
          end 
        end
      endcase
    end
  end

endmodule : arp_table
