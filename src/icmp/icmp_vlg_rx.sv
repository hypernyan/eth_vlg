
module icmp_vlg_rx 
  import
    eth_vlg_pkg::*,
    icmp_vlg_pkg::*,
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*;
#(
  parameter bit VERBOSE = 1,
  parameter string DUT_STRING = ""
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,
  ipv4.in_rx  ipv4,
  icmp.out    icmp
);

  logic [15:0] byte_cnt;
  logic        fsm_rst;
  logic [icmp_vlg_pkg::ICMP_HDR_LEN-1:0][7:0] hdr;
  logic receiving, hdr_done, err_len;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      hdr_done  <= 0;
      receiving <= 0;
      err_len   <= 0;
    end
    else begin
      if (ipv4.strm.sof && ipv4.strm.val && (ipv4.meta.ipv4_hdr.proto == ICMP) && !icmp.busy) begin // Latch header if tx is not busy
        icmp.meta.mac_hdr  <= ipv4.meta.mac_hdr;
        icmp.meta.ipv4_hdr <= ipv4.meta.ipv4_hdr;
        icmp.meta.length   <= ipv4.meta.pld_len;
        receiving <= 1;
      end
      if (icmp.strm.eof) receiving <= 0; // Deassert flag
      hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1:1] <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-2:0]; // Write to header and shift it 
      if (receiving && byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN) hdr_done <= 1; // Header done, pld time
      if (receiving && ipv4.strm.eof && byte_cnt != ipv4.meta.pld_len) err_len <= !ipv4.strm.eof; // Check for length error
    end
  end
  
  assign icmp.strm.err = (err_len || ipv4.strm.err); // Assert error if IP gets an error too
  always_ff @ (posedge clk) fsm_rst <= (icmp.done || icmp.strm.err || rst); // Reset if done or error
  
  assign hdr[0] = ipv4.strm.dat;
  
  // Output
  always_ff @ (posedge clk) begin
    if (fsm_rst)  begin
      icmp.strm.dat <= 0;
      icmp.strm.sof <= 0;
      icmp.strm.eof <= 0;
      byte_cnt <= 0;
    end
    else begin
      if (ipv4.strm.val && (ipv4.meta.ipv4_hdr.proto == ICMP)) byte_cnt <= byte_cnt + 1;
      icmp.strm.dat <= ipv4.strm.dat;
      icmp.strm.sof <= (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN);
      icmp.strm.eof <= receiving && ipv4.strm.eof;
    end
  end
  
  assign icmp.strm.val = (hdr_done && receiving && (icmp.meta.icmp_hdr.icmp_type == 0)); // Only parse Echo request
  
  // Latch header
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      icmp.meta.icmp_hdr <= '0;
      icmp.meta.val <= '0;
    end
    else begin
      if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 1) begin
        if (VERBOSE) begin
          case (hdr[7])
            0 : $display("[", DUT_STRING, "]<- ICMP request from %d:%d:%d:%d.",
              ipv4.meta.ipv4_hdr.src_ip[3], 
              ipv4.meta.ipv4_hdr.src_ip[2],
              ipv4.meta.ipv4_hdr.src_ip[1],
              ipv4.meta.ipv4_hdr.src_ip[0]
            );
            8 : $display("[", DUT_STRING, "]<- ICMP reply from %d:%d:%d:%d.",
              ipv4.meta.ipv4_hdr.src_ip[3], 
              ipv4.meta.ipv4_hdr.src_ip[2],
              ipv4.meta.ipv4_hdr.src_ip[1],
              ipv4.meta.ipv4_hdr.src_ip[0]
            );
            default : $display("[", DUT_STRING, "]<- unknown ICMP reply");
          endcase
        end
        case (hdr[7]) // Assemble 
          0 : icmp.meta.icmp_hdr.icmp_type <= 8;
          8 : icmp.meta.icmp_hdr.icmp_type <= 0;
          default : icmp.meta.icmp_hdr.icmp_type <= 'b1;
        endcase
        icmp.meta.icmp_hdr.icmp_code <= hdr[6];
        icmp.meta.icmp_hdr.icmp_cks  <= hdr[5:4]; 
        icmp.meta.icmp_hdr.icmp_id   <= hdr[3:2]; 
        icmp.meta.icmp_hdr.icmp_seq  <= hdr[1:0]; 
        icmp.meta.val                <= 1; 
      end
    end
  end

endmodule : icmp_vlg_rx
