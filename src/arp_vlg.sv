import arp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface arp_data ();
  ipv4_t      ipv4_addr;
  mac_addr_t  mac_addr;
  logic       val;
  modport in  (input  ipv4_addr, mac_addr, val);
  modport out (output ipv4_addr, mac_addr, val);
endinterface

module arp_vlg #(
  parameter VERBOSE = 1
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,
    // table interface
  input  ipv4_t ipv4_req,
  output mac_addr_t mac_rsp,
  output logic arp_val,
  output logic arp_err,
    // remote request
  mac.in      rx,
  mac.out     tx
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
  .rx   (rx),
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
  .tx   (tx),
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
    hdr_tx.src_mac_addr  <= dev.mac_addr;
    hdr_tx.src_ipv4_addr <= dev.ipv4_addr;
    hdr_tx.dst_mac_addr  <= hdr_rx.src_mac_addr;
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
  .ARP_TABLE_SIZE (4),
  .VERBOSE (VERBOSE)
) arp_table_inst (
  .clk       (clk),
  .rst       (rst),

  .arp_in    (arp_data_in),
  .dev       (dev),

  .ipv4_req  (ipv4_req),
  .mac_rsp   (mac_rsp),
  .arp_val   (arp_val),
  .arp_err   (arp_err),

  .hdr_tx    (hdr_tx_req),
  .send_req  (send_req),
  .tx_busy   (tx_busy)
);

// Update ARP entries with data from received IPv4 packets. Ignore broadcast packets
assign arp_data_in.val       = rx_done;
assign arp_data_in.mac_addr  = hdr_rx.src_mac_addr;
assign arp_data_in.ipv4_addr = hdr_rx.src_ipv4_addr;

endmodule : arp_vlg

module arp_vlg_rx #(
  parameter VERBOSE = 1)
(
  input  logic     clk,
  input  logic     rst,

  input  dev_t     dev,
  output arp_hdr_t hdr,
  mac.in           rx,
  output logic     send,
  output logic     done
);

localparam [5:0] LEN = 45;
localparam [4:0] ARP_LEN = 27;

logic [7:0] rx_d;
logic       rx_v;

assign rx_d = rx.d;
assign rx_v = rx.v;

logic [ARP_LEN-1:0][7:0] cur_hdr;
logic [5:0] byte_cnt;
logic fsm_rst;
logic err;
assign err = (rx.v && byte_cnt == LEN+1);
assign fsm_rst = (done || rst || err || rx.err);

assign cur_hdr[0] = rx.d;

always @ (posedge clk) begin
  if (fsm_rst) begin
    cur_hdr[ARP_LEN-1:1] <= 0;
    done <= 0;
    byte_cnt <= 0;
  end
  else if (rx.v && rx.hdr.ethertype == 16'h0806) begin
    cur_hdr[ARP_LEN-1:1] <= cur_hdr[ARP_LEN-2:0];
    byte_cnt <= byte_cnt + 1;
    if (byte_cnt == ARP_LEN) hdr <= cur_hdr;
    if (byte_cnt == LEN) done <= 1;
  end
end

assign send = (done && !rx.v && hdr.dst_ipv4_addr == dev.ipv4_addr && hdr.oper == 1);

always @ (posedge clk) begin
  if (done && !rx.v && VERBOSE) begin
    $display("->%d.%d.%d.%d: ARP request from %d.%d.%d.%d at %h:%h:%h:%h:%h:%h to %d.%d.%d.%d at %h:%h:%h:%h:%h:%h",
      dev.ipv4_addr[3],
      dev.ipv4_addr[2],
      dev.ipv4_addr[1],
      dev.ipv4_addr[0],
      hdr.src_ipv4_addr[3],
      hdr.src_ipv4_addr[2],
      hdr.src_ipv4_addr[1],
      hdr.src_ipv4_addr[0],
      hdr.src_mac_addr[5],
      hdr.src_mac_addr[4],
      hdr.src_mac_addr[3],
      hdr.src_mac_addr[2],
      hdr.src_mac_addr[1],
      hdr.src_mac_addr[0],
      hdr.dst_ipv4_addr[3],
      hdr.dst_ipv4_addr[2],
      hdr.dst_ipv4_addr[1],
      hdr.dst_ipv4_addr[0],
      hdr.dst_mac_addr[5],
      hdr.dst_mac_addr[4],
      hdr.dst_mac_addr[3],
      hdr.dst_mac_addr[2],
      hdr.dst_mac_addr[1],
      hdr.dst_mac_addr[0]
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

  input  dev_t dev,
  mac.out      tx,
  input  arp_hdr_t hdr,
  input  logic send,
  input  logic [15:0] len,
  output logic done,
  output logic busy
);

localparam [5:0] LEN = 46;
logic      [7:0] tx_d;
logic            tx_v;
logic [arp_vlg_pkg::HDR_LEN-1:0][7:0] cur_hdr;
logic [5:0] byte_cnt;
logic fsm_rst;

assign tx_d = tx.d;
assign tx_v = tx.v;

assign tx.hdr.ethertype    = 16'h0806;
assign tx.hdr.src_mac_addr = dev.mac_addr;

arp_fsm_t fsm;
always @ (posedge clk) begin
  if (fsm_rst) begin
    fsm      <= arp_idle_s;
    byte_cnt <= 0;
    tx.v     <= 0;
    done     <= 0;
    busy     <= 0;
  end
  else begin
    case (fsm)
      arp_idle_s : begin
        if (send) begin
          busy <= 1;
          tx.v <= 1;
          fsm <= arp_hdr_s;
          tx.hdr.dst_mac_addr <= hdr.dst_mac_addr; // destination mac from header
          tx.hdr.tag <= 0; // assume zero, to be tested
          tx.hdr.length <= len;
          if (VERBOSE) $display("<-%d.%d.%d.%d: ARP (op. %d) to %d.%d.%d.%d at %h:%h:%h:%h:%h:%h",
            dev.ipv4_addr[3],
            dev.ipv4_addr[2],
            dev.ipv4_addr[1],
            dev.ipv4_addr[0],
            hdr.oper,
            hdr.dst_ipv4_addr[3],
            hdr.dst_ipv4_addr[2],
            hdr.dst_ipv4_addr[1],
            hdr.dst_ipv4_addr[0],
            hdr.dst_mac_addr[5],
            hdr.dst_mac_addr[4],
            hdr.dst_mac_addr[3],
            hdr.dst_mac_addr[2],
            hdr.dst_mac_addr[1],
            hdr.dst_mac_addr[0]
          );
        end
        cur_hdr <= {16'd1, hdr.proto, 8'd6, 8'd4, hdr.oper, dev.mac_addr, dev.ipv4_addr, hdr.dst_mac_addr, hdr.dst_ipv4_addr};
      end
      arp_hdr_s : begin
        byte_cnt <= byte_cnt + 1;
        cur_hdr[arp_vlg_pkg::HDR_LEN-1:1] <= cur_hdr[arp_vlg_pkg::HDR_LEN-2:0];
        if (byte_cnt == LEN-2) done <= 1;
      end
    endcase
  end
end

assign fsm_rst = (done || rst);

assign tx.d = cur_hdr[arp_vlg_pkg::HDR_LEN-1];

endmodule : arp_vlg_tx

// Handle data storage and logic requests 
// to acquire destination MAC
module arp_table #(
    parameter int ARP_TABLE_SIZE = 2,
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

  input ipv4_t      ipv4_req,
  output mac_addr_t mac_rsp,
  output logic      arp_val,
  output logic      arp_err
);

logic [ARP_TABLE_SIZE-1:0] w_ptr;
logic [ARP_TABLE_SIZE-1:0] arp_table_a_a_prev;
logic [ARP_TABLE_SIZE-1:0] arp_table_a_b_prev;

fifo_sc_if #(2, 80) fifo(.*);
fifo_sc    #(2, 80) arp_fifo_inst(.*);

ipv4_t     fifo_ipv4_addr;
mac_addr_t fifo_mac_addr;

assign fifo.clk = clk;
assign fifo.rst = rst;
assign fifo.write = arp_in.val; // Write every new MAC-IP pair to fifo 
assign fifo.data_in = {arp_in.ipv4_addr, arp_in.mac_addr};
assign {fifo_ipv4_addr, fifo_mac_addr} = fifo.data_out;

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

ram_if_dp #(ARP_TABLE_SIZE, 80) arp_table(.*); // IPv4 bits = 32, MAC bits = 48;
ram_dp #(ARP_TABLE_SIZE, 80) arp_table_inst (.mem_if (arp_table)); // IPv4 bits = 32, MAC bits = 48;
assign arp_table.clk_a = clk;
assign arp_table.clk_b = clk;

assign arp_table.d_a = {fifo_ipv4_addr, fifo_mac_addr}; // Always rewrite entries from fifo
assign arp_table.d_b = {ipv4_addr_d_b, mac_addr_d_b};

assign {ipv4_addr_q_a, mac_addr_q_a} = arp_table.q_a;
assign {ipv4_addr_q_b, mac_addr_q_b} = arp_table.q_b;

logic [ARP_TABLE_SIZE-1:0] arp_table_a_a;
logic [ARP_TABLE_SIZE-1:0] arp_table_a_b;
logic [79:0]               arp_table_d_a;
logic [79:0]               arp_table_d_b;
logic [79:0]               arp_table_q_a;
logic [79:0]               arp_table_q_b;
logic                      arp_table_w_a;
logic                      arp_table_w_b;

assign arp_table_a_a = arp_table.a_a;
assign arp_table_a_b = arp_table.a_b;
assign arp_table_d_a = arp_table.d_a;
assign arp_table_d_b = arp_table.d_b;
assign arp_table_q_a = arp_table.q_a;
assign arp_table_q_b = arp_table.q_b;
assign arp_table_w_a = arp_table.w_a;
assign arp_table_w_b = arp_table.w_b;

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
          if (!fifo.empty) begin // Received new ARP packet
            fifo.read <= 1;
          end
          if (fifo.read) begin // Delay by 1
            w_fsm <= w_scan_s;
            fifo.read <= 0;
          end
        end
        w_scan_s : begin
            arp_table.a_a <= arp_table.a_a + 1; // Scanning table...
            arp_table_a_a_prev <= arp_table.a_a;
            if (fifo_ipv4_addr == ipv4_addr_q_a) begin
            w_fsm <= w_upd_s;
            if (VERBOSE) $display("%d.%d.%d.%d: ARP entry for %d:%d:%d:%d. Old:%h:%h:%h:%h:%h:%h. New:%h:%h:%h:%h:%h:%h.",
              dev.ipv4_addr[3],
              dev.ipv4_addr[2],
              dev.ipv4_addr[1],
              dev.ipv4_addr[0],
              fifo_ipv4_addr[3],
              fifo_ipv4_addr[2],
              fifo_ipv4_addr[1],
              fifo_ipv4_addr[0],
              mac_addr_q_a[5],
              mac_addr_q_a[4],
              mac_addr_q_a[3],
              mac_addr_q_a[2],
              mac_addr_q_a[1],
              mac_addr_q_a[0],
              fifo_mac_addr[5],
              fifo_mac_addr[4],
              fifo_mac_addr[3],
              fifo_mac_addr[2],
              fifo_mac_addr[1],
              fifo_mac_addr[0]
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
              fifo_ipv4_addr[3],
              fifo_ipv4_addr[2],
              fifo_ipv4_addr[1],
              fifo_ipv4_addr[0],
              fifo_mac_addr[5],
              fifo_mac_addr[4],
              fifo_mac_addr[3],
              fifo_mac_addr[2],
              fifo_mac_addr[1],
              fifo_mac_addr[0]
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

ipv4_t ipv4_req_reg;
logic to_rst;
logic arp_timeout;
// Scan/request ARP and readout logic
always @ (posedge clk) begin
  if (rst) begin
    ipv4_req_reg    <= '0;
    arp_table.a_b   <= 0;
    arp_table.w_b   <= 0;
    r_fsm           <= r_idle_s;
    to_rst          <= 1'b1;
    arp_val         <= 0;
    arp_timeout_ctr <= 0;
    send_req        <= 0;
    arp_err         <= 0;
  end
  else begin
    case (r_fsm)
      r_idle_s : begin
        arp_timeout_ctr <= 0;
        arp_err <= 0;
        to_rst <= 1'b1;
        arp_table.a_b <= 0;
        ipv4_req_reg <= ipv4_req;
        if ((ipv4_req != ipv4_req_reg) && (ipv4_req != '0)) begin
          arp_val <= 0;
          r_fsm <= r_scan_s;
          $display("*** ARP TABLE *** Requesting MAC for %d:%d:%d:%d.",
            ipv4_req[3],
            ipv4_req[2],
            ipv4_req[1],
            ipv4_req[0]
          );
        end
      end
      r_scan_s : begin
        arp_table.a_b <= arp_table.a_b + 1;
        arp_table_a_b_prev <= arp_table.a_b;
        if (ipv4_addr_q_b == ipv4_req_reg) begin
          mac_rsp <= mac_addr_q_b;
          arp_val <= 1;
          r_fsm <= r_idle_s;
          $display("*** ARP TABLE *** Request complete: found entry for %d:%d:%d:%d at %h:%h:%h:%h:%h:%h.",
              ipv4_req_reg[3],
              ipv4_req_reg[2],
              ipv4_req_reg[1],
              ipv4_req_reg[0],
              mac_addr_q_b[5],
              mac_addr_q_b[4],
              mac_addr_q_b[3],
              mac_addr_q_b[2],
              mac_addr_q_b[1],
              mac_addr_q_b[0]
           );
        end
        else if (arp_table.a_b == 0 && arp_table_a_b_prev == '1) begin
          hdr_tx.hw_type       <= 1;
          hdr_tx.proto         <= 16'h0800; // ipv4
          hdr_tx.hlen          <= 6;
          hdr_tx.plen          <= 4;
          hdr_tx.oper          <= 1;
          hdr_tx.src_mac_addr  <= dev.mac_addr;
          hdr_tx.src_ipv4_addr <= dev.ipv4_addr;
          hdr_tx.dst_mac_addr  <= 48'hffffffffffff;
          hdr_tx.dst_ipv4_addr <= ipv4_req_reg;
          send_req <= 1;
          r_fsm <= r_busy_s; // request MAC
          if (VERBOSE) $display("%d.%d.%d.%d: No ARP entry found for %d:%d:%d:%d. Requesting...",
            dev.ipv4_addr[3],
            dev.ipv4_addr[2],
            dev.ipv4_addr[1],
            dev.ipv4_addr[0],
            ipv4_req_reg[3],
            ipv4_req_reg[2],
            ipv4_req_reg[1],
            ipv4_req_reg[0]
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
        if (arp_in.val && arp_in.ipv4_addr == ipv4_req_reg) begin
          mac_rsp <= arp_in.mac_addr;
          send_req <= 0;
          to_rst <= 0;
          arp_val <= 1;
          r_fsm <= r_idle_s;
          if (VERBOSE) $display("%d.%d.%d.%d: Received ARP reply for %d:%d:%d:%d at %h:%h:%h:%h:%h:%h.",
            dev.ipv4_addr[3],
            dev.ipv4_addr[2],
            dev.ipv4_addr[1],
            dev.ipv4_addr[0],
            ipv4_req_reg[3],
            ipv4_req_reg[2],
            ipv4_req_reg[1],
            ipv4_req_reg[0],
            arp_in.mac_addr[5],
            arp_in.mac_addr[4],
            arp_in.mac_addr[3],
            arp_in.mac_addr[2],
            arp_in.mac_addr[1],
            arp_in.mac_addr[0]
          );
        end
        else if (arp_timeout_ctr == ARP_TIMEOUT_TICKS) begin
          arp_err <= 1;
          r_fsm <= r_idle_s;
          if (VERBOSE) $display("%d.%d.%d.%d: No ARP reply for %d:%d:%d:%d. Error",
            dev.ipv4_addr[3],
            dev.ipv4_addr[2],
            dev.ipv4_addr[1],
            dev.ipv4_addr[0],
            ipv4_req_reg[3],
            ipv4_req_reg[2],
            ipv4_req_reg[1],
            ipv4_req_reg[0]
          );
        end 
      end
    endcase
  end
end

endmodule : arp_table
