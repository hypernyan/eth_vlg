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
  input  logic    clk,
  input  logic    rst,
  mac_ifc.out_tx  mac,
  ipv4_ifc.in_tx  ipv4,
  input  dev_t    dev,
  // ARP table request/response
  arp_tbl_ifc.out arp_tbl
);

  logic fsm_rst;
  logic hdr_done;
  logic calc;
  logic cks_done;
  
  logic [IPV4_HDR_LEN-1:0][7:0] hdr;
  logic [15:0] byte_cnt;
  
  
  logic [15:0] cks;
  logic [19:0] cks_carry;
  // logic calc_done;

  ipv4_meta_t cur_meta;
  enum logic [3:0] {idle_s, arp_req_s, prep_s, active_s} fsm;

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm           <= idle_s;
      ipv4.err      <= 0;
      mac.meta      <= 0; 
      arp_tbl.ipv4  <= 0;
      arp_tbl.req   <= 0;
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
            fsm <= (ipv4.meta.mac_known || (ipv4.meta.ipv4_hdr.dst_ip == '1)) ? prep_s : arp_req_s;
            calc <= 1;
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
            cur_meta     <= ipv4.meta;
            ipv4.acc     <= 1;
          end
        end
        arp_req_s : begin
          calc <= 0;
          ipv4.acc <= 0;
          arp_tbl.ipv4 <= cur_meta.ipv4_hdr.dst_ip;
          if (arp_tbl.val) begin
            arp_tbl.req <= 0;
            fsm <= prep_s;
            mac.meta.hdr.dst_mac <= arp_tbl.mac;
          end
          else if (arp_tbl.err) begin
            ipv4.err <= 1;
          end
          else arp_tbl.req <= 1;
        end
        prep_s : begin
          calc <= 0;
          ipv4.acc <= 0;
          mac.rdy <= !mac.req;
          if (mac.req) begin
            fsm <= active_s;
          end
          else if (cks_done) hdr[9:8] <= cks;
        end
        active_s : begin
          arp_tbl.req <= 0;
          hdr <= hdr << $bits(byte);
        end
        default :;
      endcase
    end
  end

  always_ff @ (posedge clk) 
    if (fsm_rst) hdr_done <= 0;
    else if (byte_cnt == IPV4_HDR_LEN-1) hdr_done <= 1; // Done transmitting header, switch to buffer output
  
  always_ff @ (posedge clk)
    if (ipv4.strm.sof) ipv4.req <= 0;
    else if (byte_cnt == IPV4_HDR_LEN-4) ipv4.req <= 1; // Read out data from buffer. It takes logic 4 ticks to start output
  
  always_ff @ (posedge clk) if (fsm_rst) byte_cnt <= 0; else if (mac.strm.val) byte_cnt <= byte_cnt + 1; 

  always_ff @ (posedge clk) fsm_rst <= (mac.strm.eof || ipv4.err);

  logic sof, eof, val;

  always_comb begin
    mac.strm.dat = (hdr_done) ? ipv4.strm.dat : hdr[IPV4_HDR_LEN-1];
    mac.strm.val = val;
    mac.strm.sof = sof;
    mac.strm.eof = eof;
  end

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      val <= 0;
      sof <= 0;
      eof <= 0;
    end
    else begin
      if (mac.req) val <= 1; else if (mac.strm.eof) val <= 0;
      sof <= !val && mac.req;
      eof <= ipv4.strm.val && (byte_cnt == mac.meta.length - 2);
    end
  end

  eth_vlg_checksum #(
    .BYTES_POW    (1),
    .LENGTH_BYTES (IPV4_HDR_LEN)
  ) checksum_inst (
    .clk  (clk),
    .rst  (fsm_rst),
    .data (hdr),
    .calc (calc),
    .len  (IPV4_HDR_LEN),
    .init (0),
    .cks  (cks),    
    .done (cks_done)
  );

endmodule : ipv4_vlg_tx
