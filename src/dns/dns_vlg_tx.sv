module dns_vlg_tx
  import 
    eth_vlg_pkg::*,
    dns_vlg_pkg::*,
    udp_vlg_pkg::*,
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*;
#(
  parameter bit VERBOSE = 1,
  parameter string DUT_STRING = ""
)
(
  input logic     clk,
  input logic     rst,
  udp_ifc.out_tx  udp,
  dns_ifc.in      dns
);

  logic fsm_rst;


  logic [DNS_TOT_LEN-1:0][7:0] txd;
  
  always_ff @ (posedge clk) begin
    udp.meta.udp_hdr.src_port <= DNS_RND_PORT;
    udp.meta.udp_hdr.dst_port <= DNS_PORT;
    udp.meta.udp_hdr.cks      <= 0; // checksum skipped
    udp.meta.udp_hdr.length   <= UDP_HDR_LEN + dns.meta.length;
    udp.meta.mac_known        <= 0;
    udp.meta.ipv4_hdr.dst_ip  <= dns.meta.dns_ipv4;
    udp.meta.ipv4_hdr.id      <= 0;
  end
  
  logic [$clog2(DNS_TOT_LEN+1)-1:0] byte_cnt;

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      dns.done     <= 0;
      byte_cnt     <= 0;
      udp.rdy      <= 0;
      udp.strm.sof <= 0;
      udp.strm.val <= 0;
      udp.strm.dat <= 0;
      udp.strm.eof <= 0;
      txd          <= 0;
    end
    else begin
      if (dns.val) begin
        txd <= {dns.meta.hdr, dns.meta.qry};
        udp.rdy <= 1;   // indicate UDP that fame is ready
      end
      else if (udp.req) begin
        udp.strm.val <= 1;
        udp.strm.sof <= (byte_cnt == 0);
        udp.strm.eof <= (byte_cnt == dns.meta.length);
        udp.strm.dat <= txd[DNS_TOT_LEN-1];
        txd <= txd << $bits(byte);
        byte_cnt <= byte_cnt + 1;
      end
    end
  end

endmodule : dns_vlg_tx