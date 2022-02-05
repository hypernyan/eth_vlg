
module dns_vlg_rx 
 // import
 //   eth_vlg_pkg::*,
 //   dns_vlg_pkg::*,
 //   ipv4_vlg_pkg::*,
 //   mac_vlg_pkg::*;
#(
  parameter bit VERBOSE = 1,
  parameter string DUT_STRING = ""
)
(
  input logic    clk,
  input logic    rst,
  udp_ifc.in_rx udp,
  dns_ifc.out   dns
);
/*
  logic [15:0] byte_cnt;
  logic        fsm_rst;
  logic [dns_vlg_pkg::dns_HDR_LEN-1:0][7:0] hdr;
  logic receiving, hdr_done, err_len;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      hdr_done  <= 0;
      receiving <= 0;
      err_len   <= 0;
    end
    else begin
      if (ipv4.strm.sof && ipv4.strm.val && (ipv4.meta.ipv4_hdr.proto == dns) && !dns.busy) begin // Latch header if tx is not busy
        dns.meta.mac_hdr  <= ipv4.meta.mac_hdr;
        dns.meta.ipv4_hdr <= ipv4.meta.ipv4_hdr;
        dns.meta.length   <= ipv4.meta.pld_len;
        receiving <= 1;
      end
      if (dns.strm.eof) receiving <= 0; // Deassert flag
      hdr[dns_vlg_pkg::dns_HDR_LEN-1:1] <= {hdr[dns_vlg_pkg::dns_HDR_LEN-2:1], ipv4.strm.dat}; // Write to header and shift it 
      if (receiving && byte_cnt == dns_vlg_pkg::dns_HDR_LEN) hdr_done <= 1; // Header done, pld time
      if (receiving && ipv4.strm.eof && byte_cnt != ipv4.meta.pld_len) err_len <= !ipv4.strm.eof; // Check for length error
    end
  end
  
  //assign dns.strm.err = (err_len || ipv4.strm.err); // Assert error if IP gets an error too
  always_ff @ (posedge clk) fsm_rst <= (dns.done || dns.strm.err || rst); // Reset if done or error

  logic [7:0] dat;
  logic       sof;
  logic       eof;
  
  // Output
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      dat <= 0;
      sof <= 0;
      eof <= 0;
      byte_cnt <= 0;
    end
    else begin
      if (ipv4.strm.val && (ipv4.meta.ipv4_hdr.proto == dns)) byte_cnt <= byte_cnt + 1;
      dat <= ipv4.strm.dat;
      sof <= (byte_cnt == dns_vlg_pkg::dns_HDR_LEN);
      eof <= receiving && ipv4.strm.eof;
    end
  end
  
  always_comb begin
    dns.strm.val = (hdr_done && receiving && (dns.meta.dns_hdr.dns_type == 0)); // Only parse Echo request
    dns.strm.dat = dat;
    dns.strm.sof = sof;
    dns.strm.eof = eof;
  end

  // Latch header
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      dns.meta.dns_hdr <= '0;
      dns.meta.val <= '0;
    end
    else begin
      if (byte_cnt == dns_vlg_pkg::dns_HDR_LEN - 1) begin
        if (VERBOSE) begin
          case (hdr[7])
            0 : $display("[", DUT_STRING, "]<- dns request from %d:%d:%d:%d.",
              ipv4.meta.ipv4_hdr.src_ip[3], 
              ipv4.meta.ipv4_hdr.src_ip[2],
              ipv4.meta.ipv4_hdr.src_ip[1],
              ipv4.meta.ipv4_hdr.src_ip[0]
            );
            8 : $display("[", DUT_STRING, "]<- dns reply from %d:%d:%d:%d.",
              ipv4.meta.ipv4_hdr.src_ip[3], 
              ipv4.meta.ipv4_hdr.src_ip[2],
              ipv4.meta.ipv4_hdr.src_ip[1],
              ipv4.meta.ipv4_hdr.src_ip[0]
            );
            default : $display("[", DUT_STRING, "]<- unknown dns reply");
          endcase
        end
        case (hdr[7]) // Assemble 
          0 : dns.meta.dns_hdr.dns_type <= 8;
          8 : dns.meta.dns_hdr.dns_type <= 0;
          default : dns.meta.dns_hdr.dns_type <= 'b1;
        endcase
        dns.meta.dns_hdr.dns_code <= hdr[6];
        dns.meta.dns_hdr.dns_cks  <= hdr[5:4]; 
        dns.meta.dns_hdr.dns_id   <= hdr[3:2]; 
        dns.meta.dns_hdr.dns_seq  <= {hdr[1], ipv4.strm.dat}; 
        dns.meta.val                <= 1; 
      end
    end
  end
*/
endmodule : dns_vlg_rx
