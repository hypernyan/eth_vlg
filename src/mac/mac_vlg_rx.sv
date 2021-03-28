module mac_vlg_rx
  import
    mac_vlg_pkg::*,
    eth_vlg_pkg::*;
 #(
  parameter bit    VERBOSE = 1,
  parameter string DUT_STRING = ""

)(
  input logic clk,
  input logic rst,
  phy.in      phy,
  mac.out_rx  mac,
  input dev_t dev
);

  logic fsm_rst;
  
  logic [15:0] byte_cnt;
  
  logic fcs_detected;
  logic crc_en;
  
  logic [4:0][7:0] rxd_delay;
  logic [1:0]      rxv_delay;
    
  logic [7:0] hdr [MAC_HDR_LEN-1:0];
  
  crc32 crc32_inst(
    .clk (clk),
    .rst (fsm_rst),
    .dat (phy.dat),
    .val (crc_en),
    .ok  (fcs_detected),
    .crc ()
  );
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      byte_cnt     <= 0;
      crc_en       <= 0;
      mac.strm.val <= 0;
      mac.strm.sof <= 0;
    end
    else begin
      mac.strm.sof <= (byte_cnt == 27);  
      if (phy.val) begin // Write to header and shift it
        hdr[0] <= rxd_delay[4];
        hdr[MAC_HDR_LEN-1:1] <= hdr[MAC_HDR_LEN-2:0]; 
        byte_cnt <= byte_cnt + 1;
      end
      if (byte_cnt == 7) crc_en <= 1;
      if (byte_cnt == 27) begin
        mac.strm.val <= 1;
        mac.meta.hdr.ethertype <= {hdr[1],  hdr[0]};
        mac.meta.hdr.src_mac   <= {hdr[7],  hdr[6],  hdr[5],  hdr[4],  hdr[3], hdr[2]};
        mac.meta.hdr.dst_mac   <= {hdr[13], hdr[12], hdr[11], hdr[10], hdr[9], hdr[8]};
      end
    end
  end

  always_ff @ (posedge clk) begin
    rxd_delay[4:0] <= {rxd_delay[3:0], phy.dat};
    rxv_delay[1:0] <= {rxv_delay[0], phy.val};
    fsm_rst <= (fcs_detected || mac.strm.err || rst);
    if (VERBOSE) if (fcs_detected) $display("[", DUT_STRING, "]-> Eth from %h:%h:%h:%h:%h:%h. Ethertype: %h",
      mac.meta.hdr.src_mac[5],
      mac.meta.hdr.src_mac[4],
      mac.meta.hdr.src_mac[3],
      mac.meta.hdr.src_mac[2],
      mac.meta.hdr.src_mac[1],
      mac.meta.hdr.src_mac[0],
     //mac.meta.hdr.dst_mac[5],
     //mac.meta.hdr.dst_mac[4],
     //mac.meta.hdr.dst_mac[3],
     //mac.meta.hdr.dst_mac[2],
     //mac.meta.hdr.dst_mac[1],
     //mac.meta.hdr.dst_mac[0],
      mac.meta.hdr.ethertype
    );
    mac.strm.dat <= rxd_delay[4];
    mac.strm.err = (!phy.val && rxv_delay[0] && !fcs_detected);
    mac.strm.eof <= fcs_detected;
  end

endmodule : mac_vlg_rx
