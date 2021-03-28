module arp_vlg_table
  import
    arp_vlg_pkg::*,
    mac_vlg_pkg::*,
    eth_vlg_pkg::*;
  #(
  parameter int TABLE_SIZE = 2,
  parameter int ARP_TIMEOUT_TICKS = 1000000,
  parameter string DUT_STRING = "",
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

  arp_tbl.in        tbl
);

  logic [TABLE_SIZE-1:0] w_ptr;
  logic [TABLE_SIZE-1:0] arp_table_a_a_prev;
  logic [TABLE_SIZE-1:0] arp_table_a_b_prev;
  
  ipv4_t     cur_ipv4_addr;
  mac_addr_t cur_mac_addr;
  
  ipv4_t     ipv4_addr_d_a;
  mac_addr_t mac_addr_d_a;
  ipv4_t     ipv4_addr_q_a;
  mac_addr_t mac_addr_q_a;
  
  ipv4_t     ipv4_addr_d_b;
  mac_addr_t mac_addr_d_b;
  ipv4_t     ipv4_addr_q_b;
  mac_addr_t mac_addr_q_b;
  
  localparam MAC_ADDR_LEN = 48;
  localparam IPV4_ADDR_LEN = 32;
  
  ram_if_dp #(TABLE_SIZE, 80) arp_table (.*); // IPv4 bits = 32, MAC bits = 48;
  ram_dp    #(TABLE_SIZE, 80) arp_table_inst (.mem_if (arp_table)); // IPv4 bits = 32, MAC bits = 48;
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
  
  always_ff @ (posedge clk) begin
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
          end
          w_scan_s : begin
            arp_table.a_a <= arp_table.a_a + 1; // Scanning table...
            arp_table_a_a_prev <= arp_table.a_a;
            if (cur_ipv4_addr == ipv4_addr_q_a) begin
              w_fsm <= w_upd_s;
              if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d: ARP entry for %d:%d:%d:%d. Old:%h:%h:%h:%h:%h:%h. New:%h:%h:%h:%h:%h:%h.",
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
              if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d: No ARP entry found for %d:%d:%d:%d. Set at %h:%h:%h:%h:%h:%h.",
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
  always_ff @ (posedge clk) begin
    if (rst) begin
      ipv4_reg        <= '0;
      arp_table.a_b   <= 0;
      arp_table.w_b   <= 0;
      r_fsm           <= r_idle_s;
      tbl.val         <= 0;
      tbl.err         <= 0;
      arp_timeout_ctr <= 0;
      send_req        <= 0;
      scan_ctr        <= 0;
    end
    else begin
      case (r_fsm)
        r_idle_s : begin
          arp_timeout_ctr <= 0;
          tbl.err         <= 0;
          arp_table.a_b   <= 0;
          scan_ctr        <= 0;
          tbl.val <= 0;
          if (tbl.req) begin
            ipv4_reg <= tbl.ipv4;
            r_fsm <= r_scan_s;
            if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d: Requesting MAC for %d:%d:%d:%d.",
              dev.ipv4_addr[3],
              dev.ipv4_addr[2],
              dev.ipv4_addr[1],
              dev.ipv4_addr[0],
              tbl.ipv4[3],
              tbl.ipv4[2],
              tbl.ipv4[1],
              tbl.ipv4[0]
            );
          end
        end
        r_scan_s : begin
          scan_ctr <= scan_ctr + 1;
          arp_table.a_b <= arp_table.a_b + 1;
          arp_table_a_b_prev <= arp_table.a_b;
          if (ipv4_addr_q_b == tbl.ipv4) begin
            tbl.mac <= mac_addr_q_b;
            tbl.val <= 1;
            r_fsm <= r_idle_s;
            if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d: ARP table request complete: found entry for %d:%d:%d:%d at %h:%h:%h:%h:%h:%h.",
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
            hdr_tx.proto         <= eth_vlg_pkg::IPv4; // ipv4
            hdr_tx.hlen          <= 6;
            hdr_tx.plen          <= 4;
            hdr_tx.oper          <= 1;
            hdr_tx.src_mac       <= dev.mac_addr;
            hdr_tx.src_ipv4_addr <= dev.ipv4_addr;
            hdr_tx.dst_mac       <= mac_vlg_pkg::MAC_BROADCAST;
            hdr_tx.dst_ipv4_addr <= ipv4_reg;
            r_fsm <= r_busy_s; // request MAC
            if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d: No ARP entry found for %d:%d:%d:%d. Requesting...",
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
            tbl.mac <= arp_in.mac_addr;
            tbl.val <= 1;
            if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d: Received ARP reply for %d:%d:%d:%d at %h:%h:%h:%h:%h:%h.",
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
          if (tbl.val) begin
            r_fsm <= r_idle_s;
            tbl.val <= 0;
          end
          else if (arp_timeout_ctr == ARP_TIMEOUT_TICKS) begin
            tbl.err <= 1;
            r_fsm <= r_idle_s;
            if (VERBOSE) $display("[", DUT_STRING, "] %d.%d.%d.%d: No ARP reply for %d:%d:%d:%d.",
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

endmodule : arp_vlg_table
