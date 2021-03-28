module mac_vlg_tx
  import
    mac_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter bit    VERBOSE = 1,
  parameter string DUT_STRING = ""
)(
  input logic  clk,
  input logic  rst,
  input  dev_t dev,
  phy.out      phy,
  mac.in_tx    mac
);

  localparam MIN_DATA_PORTION = 44;
  
  enum logic [3:0] {
    idle_s,
    hdr_s,
    pld_s,
    fcs_s
  } fsm;
  
  logic fsm_rst;
  logic pad_ok;
  
  logic [3:0][7:0] crc_inv;
  logic [3:0][7:0] crc;
  logic [3:0][7:0] cur_fcs;
  logic      [7:0] dat;
  logic            crc_en;
  length_t cur_len, byte_cnt;
  
  logic [MAC_HDR_LEN-1:0] [7:0] cur_hdr;
  logic [$clog2(MAC_HDR_LEN+1)-1:0] hdr_byte_cnt;
  logic fcs, val, pld_done;
  logic [1:0] fcs_byte_cnt; 

  assign phy.clk = clk;

  crc32 crc32_inst(
    .clk (clk),
    .rst (fsm_rst),
    .dat (dat),
    .val (crc_en),
    .ok  (),
    .crc (crc_inv)
  );

  assign crc = ~crc_inv;

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm          <= idle_s;
      byte_cnt     <= 0;
      mac.req      <= 0;
      crc_en       <= 0;
      val          <= 0;
      mac.done     <= 0;
      mac.acc      <= 0;
      pad_ok       <= 0;
      pld_done     <= 0;
      cur_len      <= 0;
      hdr_byte_cnt <= 0;
      cur_fcs      <= 0;
      fcs          <= 0;
      fcs_byte_cnt <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (mac.rdy) begin
            mac.acc <= 1;
            fsm <= hdr_s;
            cur_len <= mac.meta.length;
            cur_hdr <= {PREAMBLE, mac.meta.hdr.dst_mac, dev.mac_addr, mac.meta.hdr.ethertype};
          end
        end
        hdr_s : begin
          mac.acc <= 0;
          if (hdr_byte_cnt == 8) crc_en <= 1;
          val <= 1;
          dat <= cur_hdr[MAC_HDR_LEN-1];
          cur_hdr[MAC_HDR_LEN-1:1] <= cur_hdr[MAC_HDR_LEN-2:0];
          hdr_byte_cnt <= hdr_byte_cnt + 1;
          if (hdr_byte_cnt == MAC_HDR_LEN-5) mac.req <= 1;
          if (hdr_byte_cnt == MAC_HDR_LEN-1) begin
            fsm <= pld_s;
          end
        end
        pld_s : begin
          dat <= mac.strm.dat;
          byte_cnt <= byte_cnt + 1;
          if (byte_cnt == MIN_DATA_PORTION) pad_ok <= 1;
          if (byte_cnt == cur_len - 1) begin
            pld_done <= 1;
            if (pad_ok) fsm <= fcs_s;
            mac.req <= 0;
          end
          else if (pld_done && pad_ok) fsm <= fcs_s;
        end
        fcs_s : begin
          fcs <= 1;
          crc_en <= 0;
          fcs_byte_cnt <= fcs_byte_cnt + 1;
          cur_fcs <= (fcs_byte_cnt == 1) ? crc : cur_fcs >> 8;
           if (fcs_byte_cnt == 3) begin
            if (VERBOSE) $display("[", DUT_STRING, "]-> Eth to %h:%h:%h:%h:%h:%h. Ethertype: %h",
            // dev.mac_addr[5],
            // dev.mac_addr[4],
            // dev.mac_addr[3],
            // dev.mac_addr[2],
            // dev.mac_addr[1],
            // dev.mac_addr[0],   
              mac.meta.hdr.dst_mac[5],
              mac.meta.hdr.dst_mac[4],
              mac.meta.hdr.dst_mac[3],
              mac.meta.hdr.dst_mac[2],
              mac.meta.hdr.dst_mac[1],
              mac.meta.hdr.dst_mac[0],
              mac.meta.hdr.ethertype
            );
            mac.done <= 1;
          end
        end
      endcase
    end
  end

  assign fsm_rst = (rst || mac.done);
  
  assign phy.val = val;
  assign phy.dat = fcs ? (fcs_byte_cnt == 1) ? crc[0] : cur_fcs[1] : dat;

endmodule : mac_vlg_tx
