
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
  input logic    clk,
  input logic    rst,
  input dev_t    dev,
  ipv4_ifc.in_rx ipv4,
  icmp_ifc.out   icmp
);

  logic [15:0] byte_cnt;
  logic        fsm_rst;
  logic [ICMP_HDR_LEN-1:0][7:0] hdr;
  logic receiving, err_short, err_long;

  logic [7:0] dat;
  logic       sof;
  logic       val;
  logic       eof;
  
   // Write to header and shift it 
  always_ff @ (posedge clk) hdr[ICMP_HDR_LEN-1:1] <= {hdr[ICMP_HDR_LEN-2:1], ipv4.strm.dat};

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      receiving <= 0;
      err_short   <= 0;
      err_long   <= 0;
      dat <= 0;
      sof <= 0;
      val <= 0;
      eof <= 0;
      byte_cnt <= 0;
    end
    else begin
      if (
      ipv4.strm.val &&
      (ipv4.meta.ipv4_hdr.proto == ICMP) && 
      (ipv4.meta.ipv4_hdr.dst_ip == dev.ipv4_addr) && 
      (ipv4.meta.mac_hdr.dst_mac == dev.mac_addr) &&
      !icmp.busy) begin // Latch header if tx is not busy
        if (ipv4.strm.sof) begin
          icmp.meta.mac_hdr  <= ipv4.meta.mac_hdr;
          icmp.meta.ipv4_hdr <= ipv4.meta.ipv4_hdr;
          icmp.meta.length   <= ipv4.meta.pld_len;
          receiving <= 1;
        end
        byte_cnt <= byte_cnt + 1;
      end
      if (receiving) begin
        dat <= ipv4.strm.dat;
        sof <= (byte_cnt == ICMP_HDR_LEN);
        eof <= ipv4.strm.eof;
        if (byte_cnt == ICMP_HDR_LEN) val <= 1; // Header done, pld time
        else if (icmp.strm.eof) val <= 0;
        if (byte_cnt == ipv4.meta.pld_len) err_long <= 1; // Check for length error
        if (!ipv4.strm.val) err_short <= 1; // Check for length error
      end
    end
  end
  
  //assign icmp.strm.err = (err_len || ipv4.strm.err); // Assert error if IP gets an error too
  always_ff @ (posedge clk) 
    fsm_rst <= (
      icmp.done ||
      icmp.strm.err ||
      err_long ||
      err_short ||
      rst
    ); // Reset if done or error

  always_comb begin
    icmp.strm.val = val; // Only parse Echo request
    icmp.strm.dat = dat;
    icmp.strm.sof = sof;
    icmp.strm.eof = eof;
  end

  // Latch header
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      icmp.meta.icmp_hdr <= '0;
      icmp.meta.val <= '0;
    end
    else begin
      if (byte_cnt == ICMP_HDR_LEN - 1) begin
        if (VERBOSE) begin
          case (hdr[7])
            8 : $display("[", DUT_STRING, "]<- ICMP request from %d:%d:%d:%d.",
              ipv4.meta.ipv4_hdr.src_ip[3], 
              ipv4.meta.ipv4_hdr.src_ip[2],
              ipv4.meta.ipv4_hdr.src_ip[1],
              ipv4.meta.ipv4_hdr.src_ip[0]
            );
            0 : $display("[", DUT_STRING, "]<- ICMP reply from %d:%d:%d:%d.",
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
        icmp.meta.icmp_hdr.icmp_seq  <= {hdr[1], ipv4.strm.dat}; 
      end
    end
  end

endmodule : icmp_vlg_rx
