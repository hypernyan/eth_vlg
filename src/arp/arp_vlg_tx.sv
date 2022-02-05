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
  mac_ifc.out_tx      mac,
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

  enum logic [2:0] {
    idle_s,
    wait_s,
    tx_s
  } fsm;

  stream_t strm;

  assign mac.strm.val = strm.val;
  assign mac.strm.sof = strm.sof;
  assign mac.strm.eof = strm.eof;
  assign mac.strm.dat = data[arp_vlg_pkg::ARP_HDR_LEN-1];

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm      <= idle_s;
      done     <= 0;
      busy     <= 0;
      strm.val <= 0;
      strm.sof <= 0;
      strm.eof <= 0;
      mac.meta <= 0;
      mac.rdy  <= 0;
      byte_cnt <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (send) begin
            fsm                    <= wait_s;
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
        wait_s : begin
          mac.rdy <= 1;
          if (mac.req) begin
            strm.sof <= 1;
            strm.val <= 1;
            fsm <= tx_s;
          end
        end
        tx_s : begin
          strm.sof <= 0;
          strm.val <= 1;
          strm.sof <= 0;
          byte_cnt <= byte_cnt + 1;
          data[arp_vlg_pkg::ARP_HDR_LEN-1:1] <= data[arp_vlg_pkg::ARP_HDR_LEN-2:0];
          if (byte_cnt == LEN-3) done <= 1;
          strm.eof <= done;
        end
        default : fsm <= idle_s;
      endcase
    end
  end
  
  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= done;

endmodule : arp_vlg_tx
