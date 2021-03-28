module udp_vlg_rx
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter bit    VERBOSE    = 1,
  parameter string DUT_STRING = ""
) (
  input logic clk,
  input logic rst,
  input dev_t dev,
  ipv4.in_rx  ipv4,
  udp.out_rx  udp
);

  logic [15:0] byte_cnt;
  logic [udp_vlg_pkg::UDP_HDR_LEN-1:0][7:0] hdr;
  
  // Handle incoming packets, check for errors
  logic fsm_rst, receiving, hdr_done, err_len;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      hdr_done     <= 0;
      receiving    <= 0;
      err_len      <= 0;
      hdr[udp_vlg_pkg::UDP_HDR_LEN-1:1] <= 0;
      udp.meta.ipv4_hdr <= 0;
      udp.meta.mac_hdr  <= 0;
    end
    else begin
      if (ipv4.strm.sof && (ipv4.meta.ipv4_hdr.proto == UDP)) begin
        udp.meta.mac_hdr  <= ipv4.meta.mac_hdr;
        udp.meta.ipv4_hdr <= ipv4.meta.ipv4_hdr;
        receiving         <= 1;
      end
      if (ipv4.strm.eof) receiving <= 0;
      hdr[udp_vlg_pkg::UDP_HDR_LEN-1:1] <= hdr[udp_vlg_pkg::UDP_HDR_LEN-2:0];
      if (receiving && byte_cnt == udp_vlg_pkg::UDP_HDR_LEN - 1) hdr_done <= 1;
      if (receiving && ipv4.strm.eof && byte_cnt != ipv4.meta.pld_len) err_len <= !ipv4.strm.eof;
    end
  end
  
  assign udp.strm.err = (err_len || ipv4.strm.err);
  assign hdr[0] = ipv4.strm.dat;
  
  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= (udp.strm.eof || udp.strm.err);
  
  // Output 
  
  always_ff @ (posedge clk) begin
    if (fsm_rst)  begin
      udp.strm.dat  <= 0;
      udp.strm.sof  <= 0;
      udp.strm.eof  <= 0;
      byte_cnt <= 0;
      udp.strm.val  <= 0;
    end
    else begin
      if (ipv4.strm.val && (ipv4.meta.ipv4_hdr.proto == UDP)) byte_cnt <= byte_cnt + 1;
      udp.strm.dat <= ipv4.strm.dat;
      udp.strm.sof <= (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN);
      udp.strm.eof <= receiving && ipv4.strm.eof;
      udp.strm.val <= hdr_done && receiving;
      if (udp.strm.sof && VERBOSE) $display("[", DUT_STRING, "]<- UDP from %d.%d.%d.%d:%d to %d.%d.%d.%d:%d",
          ipv4.meta.ipv4_hdr.src_ip[3], 
          ipv4.meta.ipv4_hdr.src_ip[2],
          ipv4.meta.ipv4_hdr.src_ip[1],
          ipv4.meta.ipv4_hdr.src_ip[0],
          udp.meta.udp_hdr.src_port,
          dev.ipv4_addr[3], 
          dev.ipv4_addr[2],
          dev.ipv4_addr[1],
          dev.ipv4_addr[0],
          udp.meta.udp_hdr.dst_port
        );
    end
  end
  
  // Latch header
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      udp.meta.udp_hdr.src_port <= 0;
      udp.meta.udp_hdr.dst_port <= 0; 
      udp.meta.udp_hdr.length   <= 0; 
      udp.meta.udp_hdr.cks    <= 0; 
    end
    else begin
      if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-1) begin
        udp.meta.udp_hdr.src_port <= hdr[7:6];
        udp.meta.udp_hdr.dst_port <= hdr[5:4]; 
        udp.meta.udp_hdr.length   <= hdr[3:2]; 
        udp.meta.udp_hdr.cks    <= hdr[1:0]; 
      end
    end
  end

endmodule : udp_vlg_rx
