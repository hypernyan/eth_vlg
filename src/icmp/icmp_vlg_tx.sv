
module icmp_vlg_tx 
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
  icmp.in     icmp,
  ipv4.out_tx ipv4
);

logic [7:0] hdr_tx;

logic [icmp_vlg_pkg::ICMP_HDR_LEN-1:0][7:0] hdr;
logic [7:0] byte_cnt;
logic       fsm_rst;
logic hdr_done;
logic transmitting;
logic sof;
logic val;

logic [16:0] cks_carry;
logic [15:0] cks;

fifo_sc_if #(8, 8) fifo(.*);
fifo_sc #(8, 8) fifo_inst(.*);

always_comb begin
  fifo.clk     = clk;
  fifo.rst     = fsm_rst;
  fifo.write   = icmp.strm.val;
  fifo.data_in = icmp.strm.dat;
end

always_comb begin
  ipv4.strm.sof = sof;
  ipv4.strm.eof = (ipv4.strm.val) && fifo.empty;
  ipv4.strm.val = val;
  ipv4.strm.dat = (hdr_done) ? fifo.data_out : hdr_tx;
end

assign icmp.done = ipv4.strm.eof;
assign fsm_rst = (rst || ipv4.strm.eof || icmp.strm.err);

assign cks_carry = icmp.meta.icmp_hdr.icmp_cks + 16'h0800;
assign cks = cks_carry[15:0] + cks_carry[16];

always_ff @ (posedge clk) begin
  if (fsm_rst) begin
    hdr           <= 0;
    fifo.read     <= 0;
    hdr_done      <= 0;
    val           <= 0;
    sof           <= 0;
    byte_cnt      <= 0;
    ipv4.rdy      <= 0;
    icmp.busy     <= 0;
  end
  else begin
    if (icmp.strm.sof && icmp.strm.val) begin
      if (VERBOSE) $display("[", DUT_STRING, "]-> ICMP reply to %d:%d:%d:%d",
        icmp.meta.ipv4_hdr.src_ip[3],
        icmp.meta.ipv4_hdr.src_ip[2],
        icmp.meta.ipv4_hdr.src_ip[1],
        icmp.meta.ipv4_hdr.src_ip[0]
      );
      hdr[7]   <= icmp.meta.icmp_hdr.icmp_type; // echo reply
      hdr[6]   <= 0; // code
      hdr[5:4] <= cks; // Reply with same data but the code
      hdr[3:2] <= icmp.meta.icmp_hdr.icmp_id;
      hdr[1:0] <= icmp.meta.icmp_hdr.icmp_seq;

      ipv4.meta.mac_hdr           <= icmp.meta.mac_hdr;
      ipv4.meta.mac_hdr.src_mac   <= icmp.meta.mac_hdr.src_mac; // Reply to MAC that sent ICMP request
      ipv4.meta.mac_hdr.dst_mac   <= icmp.meta.mac_hdr.src_mac; // Reply to MAC that sent ICMP request
      ipv4.meta.mac_known         <= 1;
      ipv4.meta.pld_len           <= icmp.meta.length;

      ipv4.meta.ipv4_hdr.src_ip <= dev.ipv4_addr;
      ipv4.meta.ipv4_hdr.dst_ip <= icmp.meta.ipv4_hdr.src_ip;
      ipv4.meta.ipv4_hdr.id     <= icmp.meta.ipv4_hdr.id;
      ipv4.meta.ipv4_hdr.qos    <= icmp.meta.ipv4_hdr.qos;
      ipv4.meta.ipv4_hdr.ver    <= 4;
      ipv4.meta.ipv4_hdr.proto  <= icmp.meta.ipv4_hdr.proto;
      ipv4.meta.ipv4_hdr.df     <= 0;
      ipv4.meta.ipv4_hdr.mf     <= 0;
      ipv4.meta.ipv4_hdr.ihl    <= 5;
      ipv4.meta.ipv4_hdr.ttl    <= 128;
      ipv4.meta.ipv4_hdr.cks    <= 0;
      ipv4.meta.ipv4_hdr.length <= icmp.meta.ipv4_hdr.length; // Reply with same length
      ipv4.meta.ipv4_hdr.fo     <= 0;
      ipv4.meta.ipv4_hdr.zero   <= 0;
      ipv4.rdy                  <= 1;
      icmp.busy                 <= 1;
    end
    if (ipv4.req && ipv4.rdy) begin
      hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1:1] <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-2:0];
      val <= 1;
    end
    if (val) byte_cnt <= byte_cnt + 1;
    if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 2) fifo.read <= 1; // Start reading
    if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 1) hdr_done <= 1;
    hdr_tx <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1];
    sof <= ((ipv4.req && ipv4.rdy) && !val);
  end
end

endmodule : icmp_vlg_tx
