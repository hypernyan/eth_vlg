import eth_vlg_pkg::*;
import icmp_vlg_pkg::*;
import ip_vlg_pkg::*;
import mac_vlg_pkg::*;

interface icmp;
  logic [7:0] dat;
  logic       val;
  logic       sof;
  logic       eof;
  logic       err;
  logic       busy;
  logic       done;
  icmp_meta_t meta;

  modport in  (input  dat, val, sof, eof, err, meta, output busy, done);
  modport out (output dat, val, sof, eof, err, meta, input  busy, done);
endinterface

module icmp_vlg (
  input logic clk,
  input logic rst,
  ipv4.in_rx  rx,
  ipv4.out_tx tx,
  input dev_t dev
);

icmp icmp(.*);

icmp_vlg_rx icmp_vlg_rx_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .ipv4 (rx),
  .icmp (icmp)
);
icmp_vlg_tx icmp_vlg_tx_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .ipv4 (tx),
  .icmp (icmp)
);

endmodule : icmp_vlg

module icmp_vlg_rx #(
  parameter bit VERBOSE = 1
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,
  ipv4.in_rx  ipv4,
  icmp.out    icmp
);

logic [15:0] byte_cnt;
logic        fsm_rst;

logic [icmp_vlg_pkg::ICMP_HDR_LEN-1:0][7:0] hdr;

logic receiving, hdr_done, err_len;

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr_done  <= 0;
    receiving <= 0;
    err_len  <= 0;
  end
  else begin
    if (ipv4.sof && (ipv4.meta.ipv4_hdr.proto == ICMP) && !icmp.busy) begin // Latch header if tx is not busy
      icmp.meta.mac_hdr  <= ipv4.meta.mac_hdr;
      icmp.meta.ipv4_hdr <= ipv4.meta.ipv4_hdr;
      receiving <= 1;
    end
    if (icmp.eof) receiving <= 0; // Deassert flag
    hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1:1] <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-2:0]; // Write to header and shift it 
    if (receiving && byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN) hdr_done <= 1; // Header done, payload time
    if (receiving && ipv4.eof && byte_cnt != ipv4.meta.pl_len) err_len <= !ipv4.eof; // Check for length error
  end
end

assign icmp.err = (err_len || ipv4.err); // Assert error if IP gets an error too
always @ (posedge clk) fsm_rst <= (icmp.done || icmp.err || rst); // Reset if done or error

assign hdr[0] = ipv4.dat;

// Output
always @ (posedge clk) begin
  if (fsm_rst)  begin
    icmp.dat <= 0;
    icmp.sof <= 0;
    icmp.eof <= 0;
    byte_cnt <= 0;
  end
  else begin
    if (ipv4.val && (ipv4.meta.ipv4_hdr.proto == ICMP)) byte_cnt <= byte_cnt + 1;
    icmp.dat <= ipv4.dat;
    icmp.sof <= (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN);
    icmp.eof <= receiving && ipv4.eof;
  end
end

assign icmp.val = (hdr_done && receiving && (icmp.meta.icmp_hdr.icmp_type == 0)); // Only parse Echo request

// Latch header
always @ (posedge clk) begin
  if (fsm_rst) begin
    icmp.meta.icmp_hdr <= '0;
  end
  else begin
    if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 1) begin
      if (VERBOSE)
        $display("-> srv: ICMP from %d:%d:%d:%d.",
          ipv4.meta.ipv4_hdr.src_ip[3], 
          ipv4.meta.ipv4_hdr.src_ip[2],
          ipv4.meta.ipv4_hdr.src_ip[1],
          ipv4.meta.ipv4_hdr.src_ip[0]
        );
      case (hdr[7]) // Assemble 
        0 : icmp.meta.icmp_hdr.icmp_type <= 8;
        8 : icmp.meta.icmp_hdr.icmp_type <= 0;
        default : icmp.meta.icmp_hdr.icmp_type <= 'b1;
      endcase
      icmp.meta.icmp_hdr.icmp_code  <= hdr[6];
      icmp.meta.icmp_hdr.icmp_chsum <= hdr[5:4]; 
      icmp.meta.icmp_hdr.icmp_id    <= hdr[3:2]; 
      icmp.meta.icmp_hdr.icmp_seq   <= hdr[1:0]; 
    end
  end
end

endmodule : icmp_vlg_rx

module icmp_vlg_tx #(
  parameter bit VERBOSE = 1
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

logic [16:0] chsum_carry;
logic [15:0] chsum;

fifo_sc_if #(8, 8) fifo(.*);
fifo_sc #(8, 8) fifo_inst(.*);

assign fifo.clk     = clk;
assign fifo.rst     = fsm_rst;
assign fifo.write   = icmp.val;
assign fifo.data_in = icmp.dat;
assign ipv4_hdr     = ipv4.meta.ipv4_hdr;

assign ipv4.eof = (ipv4.val) && fifo.empty;
assign icmp.done = ipv4.eof;
assign ipv4.dat = (hdr_done) ? fifo.data_out : hdr_tx;
assign fsm_rst = (rst || ipv4.eof || icmp.err);

assign chsum_carry = icmp.meta.icmp_hdr.icmp_chsum + 16'h0800;
assign chsum = chsum_carry[15:0] + chsum_carry[16];

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr          <= 0;
    fifo.read    <= 0;
    hdr_done     <= 0;
    ipv4.val       <= 0;
    byte_cnt     <= 0;
    ipv4.rdy       <= 0;
    icmp.busy    <= 0;
  end
  else begin
    if (icmp.sof && icmp.val) begin
      if (VERBOSE)
        $display("<- srv: ICMP reply to %d:%d:%d:%d",
          icmp.meta.ipv4_hdr.src_ip[3],
          icmp.meta.ipv4_hdr.src_ip[2],
          icmp.meta.ipv4_hdr.src_ip[1],
          icmp.meta.ipv4_hdr.src_ip[0]);
      hdr[7]                    <= icmp.meta.icmp_hdr.icmp_type; // echo reply
      hdr[6]                    <= 0; // code
      hdr[5:4]                  <= chsum; // Reply with same data but the code
      hdr[3:2]                  <= icmp.meta.icmp_hdr.icmp_id;
      hdr[1:0]                  <= icmp.meta.icmp_hdr.icmp_seq;

      ipv4.meta.mac_hdr         <= icmp.meta.mac_hdr;
      ipv4.meta.mac_hdr.src_mac <= icmp.meta.mac_hdr.src_mac; // Reply to MAC that sent ICMP request
      ipv4.meta.mac_hdr.dst_mac <= icmp.meta.mac_hdr.src_mac; // Reply to MAC that sent ICMP request
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
      ipv4.meta.ipv4_hdr.chsum  <= 0;
      ipv4.meta.ipv4_hdr.length <= icmp.meta.ipv4_hdr.length; // Reply with same length
      ipv4.meta.ipv4_hdr.fo     <= 0;
      ipv4.meta.ipv4_hdr.zero   <= 0;
      ipv4.rdy                  <= 1;
      icmp.busy                 <= 1;
    end
    if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 2) fifo.read <= 1; // Start reading
    if (ipv4.req && ipv4.rdy) begin
      hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1:1] <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-2:0];
      ipv4.val <= 1;
    end
    if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 1) hdr_done <= 1;
    hdr_tx <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1];
    if (ipv4.val) byte_cnt <= byte_cnt + 1;
    ipv4.sof <= ((ipv4.req && ipv4.rdy) && !ipv4.val);
  end
end

endmodule : icmp_vlg_tx
