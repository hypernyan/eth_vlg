module arp_vlg_tx 
  import
    arp_vlg_pkg::*,
    mac_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter bit VERBOSE = 1,
  parameter string DUT_STRING = ""
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

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm          <= arp_idle_s;
      done         <= 0;
      busy         <= 0;
      mac.strm.val <= 0;
      mac.strm.sof <= 0;
      mac.strm.eof <= 0;
      mac.meta     <= 0;
      mac.rdy      <= 0;
      byte_cnt     <= 0;
    end
    else begin
      case (fsm)
        arp_idle_s : begin
          if (send) begin
            fsm                    <= arp_wait_s;
            busy                   <= 1;
            mac.meta.hdr.dst_mac   <= hdr.dst_mac;
            mac.meta.hdr.ethertype <= eth_vlg_pkg::ARP;
            mac.meta.hdr.src_mac   <= dev.mac_addr;
            mac.meta.length        <= LEN;
            if (VERBOSE) begin
              if (hdr.oper == 1) $display("[", DUT_STRING, "] %d.%d.%d.%d: *ARP* Who has %d.%d.%d.%d?",
                dev.ipv4_addr[3],
                dev.ipv4_addr[2],
                dev.ipv4_addr[1],
                dev.ipv4_addr[0],
                hdr.dst_ipv4_addr[3],
                hdr.dst_ipv4_addr[2],
                hdr.dst_ipv4_addr[1],
                hdr.dst_ipv4_addr[0]
              );
              if (hdr.oper == 2) $display("[", DUT_STRING, "] %d.%d.%d.%d: *ARP* %d.%d.%d.%d is at %h:%h:%h:%h:%h:%h",
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
          mac.strm.sof <= 1;
          mac.strm.val <= 1;
        end
        arp_tx_s : begin
          mac.strm.sof <= 0;
          byte_cnt <= byte_cnt + 1;
          data[arp_vlg_pkg::ARP_HDR_LEN-1:1] <= data[arp_vlg_pkg::ARP_HDR_LEN-2:0];
          if (byte_cnt == LEN-3) done <= 1;
          mac.strm.eof <= done;
        end
      endcase
    end
  end
  
  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= done;
  
  assign mac.strm.dat = data[arp_vlg_pkg::ARP_HDR_LEN-1];

endmodule : arp_vlg_tx
