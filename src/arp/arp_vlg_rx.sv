module arp_vlg_rx
  import
    arp_vlg_pkg::*,
    mac_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter bit    VERBOSE = 1,
  parameter string DUT_STRING = ""
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
  
  logic [ARP_LEN-1:0][7:0] cur_hdr;
  logic [5:0] byte_cnt;
  logic fsm_rst;
  logic err;
  assign err = (mac.strm.val && byte_cnt == LEN+1);
  assign fsm_rst = (done || rst || err || mac.strm.err);
  
  assign cur_hdr[0] = mac.strm.dat;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      done <= 0;
      byte_cnt <= 0;
    end
    else if (mac.strm.val && mac.meta.hdr.ethertype == eth_vlg_pkg::ARP) begin
      cur_hdr[ARP_LEN-1:1] <= cur_hdr[ARP_LEN-2:0];
      byte_cnt <= byte_cnt + 1;
      if (byte_cnt == ARP_LEN) hdr <= cur_hdr;
      if (byte_cnt == LEN) done <= 1;
    end
  end
  
  assign send = (done && !mac.strm.val && hdr.dst_ipv4_addr == dev.ipv4_addr && hdr.oper == 1);
  
  always_ff @ (posedge clk) begin
    if (done && !mac.strm.val && VERBOSE) begin
      $display("[", DUT_STRING, "] %d.%d.%d.%d: ARP request from %d.%d.%d.%d at %h:%h:%h:%h:%h:%h to %d.%d.%d.%d at %h:%h:%h:%h:%h:%h",
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
