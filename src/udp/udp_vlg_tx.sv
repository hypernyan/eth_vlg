module udp_vlg_tx
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter bit    VERBOSE    = 1,
  parameter string DUT_STRING = ""

)(
  input logic     clk,
  input logic     rst,
  input dev_t     dev,
  udp_ifc.in_tx   udp,
  ipv4_ifc.out_tx ipv4
);

  logic [UDP_HDR_LEN-1:0][7:0] hdr;  
  logic [15:0] byte_cnt;
  logic hdr_done, fsm_rst, transmitting, shift;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      transmitting <= 0;
    end
    else begin
      if (udp.rdy && !transmitting) begin
        transmitting              <= 1;
        hdr                       <= udp.meta.udp_hdr;
        ipv4.meta.pld_len         <= udp.meta.udp_hdr.length;
        ipv4.meta.mac_known       <= udp.meta.mac_known;
        ipv4.meta.mac_hdr.dst_mac <= udp.meta.mac_hdr.dst_mac;
        ipv4.meta.ipv4_hdr.src_ip <= udp.meta.ipv4_hdr.src_ip; // Assigned at upper handlers
        ipv4.meta.ipv4_hdr.dst_ip <= udp.meta.ipv4_hdr.dst_ip; // Assigned at upper handlers     
        ipv4.meta.ipv4_hdr.id     <= udp.meta.ipv4_hdr.id;
        ipv4.meta.ipv4_hdr.qos    <= 0;
        ipv4.meta.ipv4_hdr.ver    <= 4;
        ipv4.meta.ipv4_hdr.proto  <= ipv4_vlg_pkg::UDP;
        ipv4.meta.ipv4_hdr.df     <= 0;
        ipv4.meta.ipv4_hdr.mf     <= 0;
        ipv4.meta.ipv4_hdr.ihl    <= 5;
        ipv4.meta.ipv4_hdr.ttl    <= 128;
        ipv4.meta.ipv4_hdr.fo     <= 0;
      end
      else if (shift) begin
        if (VERBOSE && !ipv4.strm.val) $display("[", DUT_STRING, "]-> UDP from %d.%d.%d.%d:%d to %d.%d.%d.%d:%d",
          dev.ipv4_addr[3],
          dev.ipv4_addr[2],
          dev.ipv4_addr[1],
          dev.ipv4_addr[0],
          udp.meta.udp_hdr.src_port,
          udp.meta.ipv4_hdr.dst_ip[3],
          udp.meta.ipv4_hdr.dst_ip[2],
          udp.meta.ipv4_hdr.dst_ip[1],
          udp.meta.ipv4_hdr.dst_ip[0],
          udp.meta.udp_hdr.dst_port
        );
        hdr <= hdr << $bits(byte);
      end
    end
  end


  always_ff @ (posedge clk) 
    if (fsm_rst) hdr_done <= 0;
    else if (byte_cnt == UDP_HDR_LEN-1) hdr_done <= 1; // Done transmitting header, switch to buffer output

  always_ff @ (posedge clk) 
    if (udp.strm.sof) udp.req <= 0;
    else if (byte_cnt == UDP_HDR_LEN-4) udp.req <= 1; // Done with header, requesting data
  
  always_ff @ (posedge clk) if (ipv4.req) ipv4.rdy <= 0; else if (udp.rdy && !transmitting) ipv4.rdy <= 1;

  always_ff @ (posedge clk) if (fsm_rst) shift <= 0; else if (ipv4.req) shift <= 1;

  always_ff @ (posedge clk) if (fsm_rst) byte_cnt <= 0; else if (ipv4.strm.val) byte_cnt <= byte_cnt + 1; 

  always_ff @ (posedge clk) fsm_rst <= ipv4.err || udp.strm.eof;

  logic sof, eof, val;

  always_comb begin
    ipv4.strm.dat = (hdr_done) ? udp.strm.dat : hdr[UDP_HDR_LEN-1];
    ipv4.strm.val = val;
    ipv4.strm.sof = sof;
    ipv4.strm.eof = eof;
  end

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      val <= 0;
      sof <= 0;
      eof <= 0;
    end
    else begin
      if (ipv4.req) val <= 1; else if (eof) val <= 0;
      sof <= !val && ipv4.req;
      eof <= ipv4.strm.val && (byte_cnt == ipv4.meta.pld_len - 2);
    end
  end

endmodule : udp_vlg_tx
