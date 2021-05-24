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
  input logic clk,
  input logic rst,
  input dev_t dev,
  udp.in_tx   udp,
  ipv4.out_tx ipv4
);

  logic [udp_vlg_pkg::UDP_HDR_LEN-1:0][7:0] hdr;
  logic [7:0] hdr_tx;
  
  logic [15:0] byte_cnt;
  logic hdr_done, fsm_rst, transmitting;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      hdr_done       <= 0;
      ipv4.strm.val  <= 0;
      ipv4.rdy       <= 0;
      transmitting   <= 0;
      byte_cnt       <= 0;
      udp.req        <= 0;
      ipv4.meta      <= 0;
    end
    else begin
      hdr_tx <= hdr[udp_vlg_pkg::UDP_HDR_LEN-1];
      if (ipv4.strm.val) byte_cnt <= byte_cnt + 1;
      if (udp.rdy && !transmitting) begin
        transmitting              <= 1;
        ipv4.rdy                  <= 1;
        hdr                       <= udp.meta.udp_hdr;
        ipv4.meta.pld_len         <= udp.meta.udp_hdr.length + udp_vlg_pkg::UDP_HDR_LEN;
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
        //ipv4.meta.ipv4_hdr.length <= udp.meta.udp_hdr.length + ipv4_vlg_pkg::IPV4_HDR_LEN;
       // ipv4.meta.pld_len <= udp.meta.udp_hdr.length;// + ipv4_vlg_pkg::IPV4_HDR_LEN;
                $display("ipv4.meta.pld_len", (udp.meta.udp_hdr.length));

        ipv4.meta.ipv4_hdr.fo     <= 0;
      //  $display("from udp: length %d", udp.meta.udp_hdr.length + ipv4_vlg_pkg::IPV4_HDR_LEN);
      //  $display("from udp: pl length %d")
      end
      else if (ipv4.req && ipv4.rdy) begin
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
        if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-2) udp.req <= 1; // Done with header, requesting data
        hdr[udp_vlg_pkg::UDP_HDR_LEN-1:1] <= hdr[udp_vlg_pkg::UDP_HDR_LEN-2:0];
        ipv4.strm.val <= 1;
      end
      if (byte_cnt == udp_vlg_pkg::UDP_HDR_LEN-1) hdr_done <= 1;
    end
  end
  
  assign ipv4.strm.sof = ipv4.strm.val && (byte_cnt == 0);
  
  assign ipv4.strm.eof = ipv4.strm.val && udp.strm.eof;
  assign ipv4.strm.dat = (hdr_done) ? udp.strm.dat : hdr_tx;
  assign fsm_rst = (rst || ipv4.strm.eof);

endmodule : udp_vlg_tx
