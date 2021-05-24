module ipv4_vlg_rx
  import 
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    eth_vlg_pkg::*,
    tcp_vlg_pkg::*;
#(
  parameter bit    VERBOSE = 1,
  parameter string DUT_STRING = ""
)
(
  input logic clk,
  input logic rst,
  mac.in_rx   mac,
  ipv4.out_rx ipv4,
  input dev_t dev
);

  logic [18:0] cks;
  logic [15:0] cks_rec;
  logic [15:0] cks_calc;
  logic [7:0]  cks_hi;
  logic [2:0]  cks_carry;
  logic        cks_ctl;
  logic        cks_ok;

  assign cks_carry = cks[18:16];
  assign cks_calc  = cks[15:0] + cks_carry;

  logic [15:0] byte_cnt;
  logic fsm_rst, receiving, hdr_done;

  logic [IPV4_HDR_LEN-1:0][7:0] hdr;

  // Handle incoming packets, check for errors
  logic [5:0] ihl_bytes;
  always_ff @ (posedge clk) begin
    if (fsm_rst || rst) begin
      receiving     <= 0;
      hdr_done      <= 0;
      cks           <= 0;
      cks_hi        <= 0;
      byte_cnt      <= 0;
    //  ipv4.strm.dat <= 0;
      ipv4.strm.err <= 0;
      ipv4.strm.val <= 0;
      ipv4.strm.sof <= 0;
      ipv4.strm.eof <= 0;
      ipv4.meta     <= 0;
    end
    else begin
      hdr[IPV4_HDR_LEN-1:1] <= hdr[IPV4_HDR_LEN-2:0];
      if (byte_cnt == IPV4_HDR_LEN-2) begin
        ipv4.meta.ipv4_hdr[159:0] <= hdr[19:0];
        ipv4.meta.pld_len <= hdr[17:16] - 20;
      end
      // As soon as MAC passed IPv4 packet, start receiving it
      if (mac.strm.sof && mac.strm.val && (mac.meta.hdr.ethertype == eth_vlg_pkg::IPv4)) begin
        ipv4.meta.mac_hdr <= mac.meta.hdr;
        ihl_bytes <= {mac.strm.dat[3:0], 2'b00}; // latch header length asap
        receiving <= 1; // set flag to continue
      end
      if (receiving && (byte_cnt == ihl_bytes)) hdr_done <= 1; // header is done and valid
      if (mac.strm.val) begin
        if (byte_cnt[0]) cks <= cks + {cks_hi, mac.strm.dat};
        if (!byte_cnt[0]) cks_hi <= mac.strm.dat;
        if (receiving) byte_cnt <= byte_cnt + 1;
      end
      if (receiving && (byte_cnt == IPV4_HDR_LEN - 1)) begin
        if (ipv4.meta.ipv4_hdr.dst_ip == dev.ipv4_addr || ipv4.meta.ipv4_hdr.dst_ip == IPV4_BROADCAST) ipv4.strm.val <= 1;
        ipv4.strm.sof <= 1;
      end
      else ipv4.strm.sof <= 0;
      ipv4.strm.eof <= hdr_done && (byte_cnt == ipv4.meta.ipv4_hdr.length - 2);
      if (ipv4.strm.eof) begin
        if (VERBOSE) $display("[", DUT_STRING, "]<- %d.%d.%d.%d: IPv4 from %d.%d.%d.%d",
          dev.ipv4_addr[3],
          dev.ipv4_addr[2],
          dev.ipv4_addr[1],
          dev.ipv4_addr[0],
          ipv4.meta.ipv4_hdr.src_ip[3],
          ipv4.meta.ipv4_hdr.src_ip[2],
          ipv4.meta.ipv4_hdr.src_ip[1],
          ipv4.meta.ipv4_hdr.src_ip[0]
        );
        $display("ipv4_rx id %h", ipv4.meta.ipv4_hdr.id);
      end
    end
  end
  
  always_ff @ (posedge clk) ipv4.strm.dat <= mac.strm.dat;

  assign fsm_rst = (ipv4.strm.eof || ipv4.strm.err);

  assign hdr[0] = mac.strm.dat;

  // Calculate cks
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      cks_ok <= 0;
    end
    else begin
      //if (cks_ctl && (cks_calc == '1)) begin
      if (cks_ctl) begin
        cks_ok <= 1;
      end
      else cks_ok <= 0;
      if (cks_ctl && (cks_calc != '1)) begin
        //if (fsm == ipv4_pld_s && byte_cnt == ipv4.ipv4_hdr.ihl*4) $display("IPv4 core: Bad header cks.");
      end
    end
  end

endmodule : ipv4_vlg_rx
