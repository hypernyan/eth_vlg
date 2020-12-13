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
  icmp_hdr_t  icmp_hdr;
  ipv4_hdr_t  ipv4_hdr;
  mac_hdr_t   mac_hdr;

  modport in  (input  dat, val, sof, eof, err, icmp_hdr, ipv4_hdr, mac_hdr, output busy, done);
  modport out (output dat, val, sof, eof, err, icmp_hdr, ipv4_hdr, mac_hdr, input  busy, done);
endinterface

module icmp_vlg (
  input logic clk,
  input logic rst,
  ipv4.in_rx rx,
  ipv4.out_tx tx,
  input dev_t dev
);

icmp icmp(.*);

icmp_vlg_rx icmp_vlg_rx_inst (.*);
icmp_vlg_tx icmp_vlg_tx_inst (.*);

endmodule : icmp_vlg

module icmp_vlg_rx #(
  parameter bit VERBOSE = 1
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,
  ipv4.in_rx  rx,
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
    if (rx.sof && (rx.ipv4_hdr.proto == ICMP) && !icmp.busy) begin // Latch header if tx is not busy
      icmp.mac_hdr  <= rx.mac_hdr;
      icmp.ipv4_hdr <= rx.ipv4_hdr;
      receiving <= 1;
    end
    if (icmp.eof) receiving <= 0; // Deassert flag
    hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1:1] <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-2:0]; // Write to header and shift it 
    if (receiving && byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN) hdr_done <= 1; // Header done, payload time
    if (receiving && rx.eof && byte_cnt != rx.payload_length) err_len <= !rx.eof; // Check for length error
  end
end

assign icmp.err = (err_len || rx.err); // Assert error if IP gets an error too
always @ (posedge clk) fsm_rst <= (icmp.done || icmp.err || rst); // Reset if done or error

assign hdr[0] = rx.dat;

// Output
always @ (posedge clk) begin
  if (fsm_rst)  begin
    icmp.dat <= 0;
    icmp.sof <= 0;
    icmp.eof <= 0;
    byte_cnt <= 0;
  end
  else begin
    if (rx.val && (rx.ipv4_hdr.proto == ICMP)) byte_cnt <= byte_cnt + 1;
    icmp.dat <= rx.dat;
    icmp.sof <= (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN);
    icmp.eof <= receiving && rx.eof;
  end
end

assign icmp.val = (hdr_done && receiving && (icmp.icmp_hdr.icmp_type == 0)); // Only parse Echo request

// Latch header
always @ (posedge clk) begin
  if (fsm_rst) begin
    icmp.icmp_hdr <= '0;
  end
  else begin
    if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 1) begin
      if (VERBOSE)
        $display("-> srv: ICMP from %d:%d:%d:%d.",
          rx.ipv4_hdr.src_ip[3], 
          rx.ipv4_hdr.src_ip[2],
          rx.ipv4_hdr.src_ip[1],
          rx.ipv4_hdr.src_ip[0]
        );
      case (hdr[7]) // Assemble 
        0 : icmp.icmp_hdr.icmp_type <= 8;
        8 : icmp.icmp_hdr.icmp_type <= 0;
        default : icmp.icmp_hdr.icmp_type <= 'b1;
      endcase
      icmp.icmp_hdr.icmp_code  <= hdr[6];
      icmp.icmp_hdr.icmp_chsum <= hdr[5:4]; 
      icmp.icmp_hdr.icmp_id    <= hdr[3:2]; 
      icmp.icmp_hdr.icmp_seq   <= hdr[1:0]; 
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
  ipv4.out_tx tx
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
assign ipv4_hdr     = tx.ipv4_hdr;

assign tx.eof = (tx.val) && fifo.empty;
assign icmp.done = tx.eof;
assign tx.dat = (hdr_done) ? fifo.data_out : hdr_tx;
assign fsm_rst = (rst || tx.eof || icmp.err);

assign chsum_carry = icmp.icmp_hdr.icmp_chsum + 16'h0800;
assign chsum = chsum_carry[15:0] + chsum_carry[16];

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr          <= 0;
    fifo.read    <= 0;
    hdr_done     <= 0;
    tx.val       <= 0;
    byte_cnt     <= 0;
    tx.rdy       <= 0;
    tx.broadcast <= 0;
    icmp.busy    <= 0;
  end
  else begin
    if (icmp.sof && icmp.val) begin
      if (VERBOSE)
        $display("<- srv: ICMP reply to %d:%d:%d:%d",
          icmp.ipv4_hdr.src_ip[3],
          icmp.ipv4_hdr.src_ip[2],
          icmp.ipv4_hdr.src_ip[1],
          icmp.ipv4_hdr.src_ip[0]);
      hdr[7]             <= icmp.icmp_hdr.icmp_type; // echo reply
      hdr[6]             <= 0; // code
      hdr[5:4]           <= chsum; // Reply with same data but the code
      hdr[3:2]           <= icmp.icmp_hdr.icmp_id;
      hdr[1:0]           <= icmp.icmp_hdr.icmp_seq;
      tx.mac_hdr         <= icmp.mac_hdr;
      tx.ipv4_hdr.src_ip <= dev.ipv4_addr;
      tx.ipv4_hdr.dst_ip <= icmp.ipv4_hdr.src_ip;
      tx.ipv4_hdr.id     <= icmp.ipv4_hdr.id;
      tx.ipv4_hdr.qos    <= icmp.ipv4_hdr.qos;
      tx.ipv4_hdr.ver    <= 4;
      tx.ipv4_hdr.proto  <= icmp.ipv4_hdr.proto;
      tx.ipv4_hdr.df     <= 0;
      tx.ipv4_hdr.mf     <= 0;
      tx.ipv4_hdr.ihl    <= 5;
      tx.ipv4_hdr.ttl    <= 128;
      tx.ipv4_hdr.chsum  <= 0;
      tx.ipv4_hdr.length <= icmp.ipv4_hdr.length; // Reply with same length
      tx.ipv4_hdr.fo     <= 0;
      tx.ipv4_hdr.zero   <= 0;
      tx.rdy             <= 1;
      icmp.busy          <= 1;
    end
    if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 2) fifo.read <= 1; // Start reading
    if (tx.req && tx.rdy) begin
      hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1:1] <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-2:0];
      tx.val <= 1;
    end
    if (byte_cnt == icmp_vlg_pkg::ICMP_HDR_LEN - 1) hdr_done <= 1;
    hdr_tx <= hdr[icmp_vlg_pkg::ICMP_HDR_LEN-1];
    if (tx.val) byte_cnt <= byte_cnt + 1;
    tx.sof <= ((tx.req && tx.rdy) && !tx.val);
  end
end

endmodule : icmp_vlg_tx
