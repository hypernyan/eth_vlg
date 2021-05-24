module ipv4_vlg_tx
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
  input  logic  clk,
  input  logic  rst,
  mac.out_tx    mac,
  ipv4.in_tx    ipv4,
  input  dev_t  dev,
  // ARP table request/response
  arp_tbl.out   arp_tbl
);

  parameter int CHECKSUM_CALC_POW_WIDTH = 4; // 

  logic fsm_rst;
  logic hdr_done;
  
  logic [IPV4_HDR_LEN-1:0][7:0] hdr;
  logic [15:0] byte_cnt, length;
  
  
  logic [15:0] cks;
  logic [19:0] cks_carry;
  logic calc_done;
  logic [7:0] hdr_tx;

  ipv4_meta_t cur_meta;
  enum logic [4:0] {idle_s, arp_req_s, prep_s, active_s, wait_s} fsm;
  logic [$clog2(CHECKSUM_CALC_POW_WIDTH+1)-1:0] calc_ctr;

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm           <= idle_s;
      hdr_done      <= 0;
      byte_cnt      <= 0;
      ipv4.req      <= 0;
    //  ipv4.done     <= 0;
      mac.strm      <= 0;
      mac.rdy       <= 0;
      mac.meta      <= 0; 
      arp_tbl.ipv4  <= 0;
      length        <= 0;
      arp_tbl.req   <= 0;
      calc_ctr      <= 0;
      calc_done     <= 0;
      hdr           <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (ipv4.rdy) begin
            if (VERBOSE) $display("[", DUT_STRING, "]-> %d.%d.%d.%d: IPv4 to %d.%d.%d.%d",
              dev.ipv4_addr[3],
              dev.ipv4_addr[2],
              dev.ipv4_addr[1],
              dev.ipv4_addr[0],
              ipv4.meta.ipv4_hdr.dst_ip[3],
              ipv4.meta.ipv4_hdr.dst_ip[2],
              ipv4.meta.ipv4_hdr.dst_ip[1],
              ipv4.meta.ipv4_hdr.dst_ip[0]
            );
            fsm <= (ipv4.meta.mac_known) ? prep_s : arp_req_s;
            mac.meta.length        <= ipv4.meta.pld_len + IPV4_HDR_LEN;            
            mac.meta.hdr.src_mac   <= dev.mac_addr;
            mac.meta.hdr.dst_mac   <= ipv4.meta.mac_hdr.dst_mac;
            mac.meta.hdr.ethertype <= eth_vlg_pkg::IPv4;
            hdr[19]      <= {ipv4.meta.ipv4_hdr.ver, ipv4.meta.ipv4_hdr.ihl};
            hdr[18]      <= ipv4.meta.ipv4_hdr.qos;                           
            hdr[17:16]   <= ipv4.meta.pld_len + IPV4_HDR_LEN;
            hdr[15:14]   <= ipv4.meta.ipv4_hdr.id;
            hdr[13][7]   <= 0;
            hdr[13][6]   <= ipv4.meta.ipv4_hdr.df;
            hdr[13][5]   <= ipv4.meta.ipv4_hdr.mf;
            hdr[13][4]   <= 0;
            hdr[13][3:0] <= ipv4.meta.ipv4_hdr.fo[11:8];
            hdr[12]      <= ipv4.meta.ipv4_hdr.fo[7:0];
            hdr[11]      <= ipv4.meta.ipv4_hdr.ttl;
            hdr[10]      <= ipv4.meta.ipv4_hdr.proto;
            hdr[9:8]     <= 0;
            hdr[7:4]     <= ipv4.meta.ipv4_hdr.src_ip;
            hdr[3:0]     <= ipv4.meta.ipv4_hdr.dst_ip;
            length       <= ipv4.meta.pld_len + IPV4_HDR_LEN;
            cur_meta     <= ipv4.meta;
            ipv4.acc     <= 1;
          end
        end
        arp_req_s : begin
          ipv4.acc <= 0;
          arp_tbl.ipv4 <= cur_meta.ipv4_hdr.dst_ip;
          if (arp_tbl.val) begin
            arp_tbl.req <= 0;
            fsm <= prep_s;
            mac.meta.hdr.dst_mac <= arp_tbl.mac;
          end
          else arp_tbl.req <= 1;
        end
        prep_s : begin
          ipv4.acc <= 0;
          if (calc_ctr == CHECKSUM_CALC_POW_WIDTH - 1) begin
            calc_done <= 1;
            hdr[9:8] <= cks;
          end
          else calc_ctr <= calc_ctr + 1;
          if (calc_done) mac.rdy <= 1;
          if (mac.req) fsm <= active_s;
        end
        active_s : begin
          mac.rdy <= 0;
          arp_tbl.req <= 0;
          mac.strm.sof <= (byte_cnt == 0);
          mac.strm.eof <= (byte_cnt == length - 1);
          mac.strm.val <= 1;
          mac.strm.dat <= (hdr_done) ? ipv4.strm.dat : hdr[IPV4_HDR_LEN-1];
          if (byte_cnt == length - 1) fsm <= wait_s;
          hdr[IPV4_HDR_LEN-1:1] <= hdr[IPV4_HDR_LEN-2:0];
          if (byte_cnt == IPV4_HDR_LEN-4) ipv4.req <= 1; // Read out data from buffer. It takes logic 4 ticks to start output
          if (byte_cnt == IPV4_HDR_LEN-1) hdr_done <= 1; // Done transmitting header, switch to buffer output
          byte_cnt <= byte_cnt + 1;
        end
        wait_s : begin
          mac.strm.sof <= 0;
          mac.strm.eof <= 0;
          mac.strm.val <= 0;
          mac.strm.dat <= 0;
        end
      endcase
    end
  end
  
  assign cks = ~(cks_carry[19:16] + cks_carry[15:0]); // Calculate actual cks  
  
  always_ff @ (posedge clk) ipv4.done <= (mac.done || arp_tbl.err); 

  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= ipv4.done;

  sum #(
    .W ($bits(byte)*2),
    .N (CHECKSUM_CALC_POW_WIDTH)
  ) sum_inst (
    .clk (clk),
    .in  ({{{(16*(2**4)-$bits(hdr))}{1'b0}}, hdr}),
    .res (cks_carry)
  );

endmodule : ipv4_vlg_tx
