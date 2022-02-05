// Computes length of UDP frame
module udp_vlg_tx_ctl
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int MTU = 1500
) (
  input logic        clk,
  input logic        rst,
  input dev_t        dev,
  udp_data_ifc.in_tx data,
  udp_ifc.out_tx     udp,
  udp_ctl_ifc.in     ctl
);
  
  localparam int UDP_MAX_PAYLOAD = MTU - IPV4_HDR_LEN - UDP_HDR_LEN;

  fifo_sc_ifc #(
    .D ($clog2(UDP_MAX_PAYLOAD+1)),
    .W (8)
  ) fifo (.*);

  eth_vlg_fifo_sc #(
    .D ($clog2(UDP_MAX_PAYLOAD+1)),
    .W (8)
  ) fifo_inst (fifo);
  
  logic [$clog2(UDP_MAX_PAYLOAD+1)-1:0] ctr_tx;
  logic fifo_rst;
  logic read;
  logic sof, eof, val;
  
  assign fifo.clk     = clk;
  assign fifo.rst     = fifo_rst;
  assign fifo.write   = data.val && !fifo.full;
  assign fifo.data_in = data.dat;

  enum logic [2:0] {idle_s, pend_s, tx_s} fsm;
  
  ipv4_vlg_pkg::id_t ipv4_id;

  always_ff @ (posedge clk) begin
    if (rst) begin
      fsm      <= idle_s;
      udp.rdy  <= 0;
      ctr_tx   <= 0;
      ipv4_id  <= 0;
      fifo_rst <= 1;
      read     <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          fifo_rst <= 0;
          ctr_tx   <= 0;
          read     <= 0;
          udp.meta.udp_hdr.src_port <= ctl.loc_port;
          udp.meta.udp_hdr.dst_port <= ctl.rem_port_tx;
          udp.meta.udp_hdr.length   <= (ctl.length <= UDP_MAX_PAYLOAD) ? ctl.length + udp_vlg_pkg::UDP_HDR_LEN : UDP_MAX_PAYLOAD;
          udp.meta.udp_hdr.cks      <= 0; // checksum skipped
          udp.meta.ipv4_hdr.src_ip  <= dev.ipv4_addr;
          udp.meta.ipv4_hdr.dst_ip  <= ctl.ipv4_tx;
          udp.meta.ipv4_hdr.id      <= ipv4_id;
          udp.meta.mac_known        <= 0;
          udp.meta.mac_hdr.dst_mac  <= 0;
          data.cts                  <= 1;
          if (!fifo.empty) begin
            fsm     <= pend_s;
            ipv4_id <= ipv4_id + 1;
            udp.rdy <= 1;
          end
        end
        pend_s : begin
          if (udp.req) begin
            fsm      <= tx_s;
            data.cts <= 0; // hold cts low until current datagram sent
            read     <= 1; // start reading from fifo asap
            udp.rdy  <= 0;
            sof      <= 1;
            val      <= 1;
          end
        end
        tx_s : begin
          ctr_tx <= ctr_tx + 1;
          sof <= 0;
          eof <= (ctr_tx == udp.meta.udp_hdr.length - 1);
          if (eof) begin
            val      <= 0;
            fsm      <= idle_s;
            fifo_rst <= 1;
          end
        end
        default :;
      endcase
    end
  end

  always_comb begin
    fifo.read = read || udp.req; // start reading with request as fifo has 1 tick delay
    udp.strm.dat = fifo.data_out;
    udp.strm.sof = sof;
    udp.strm.eof = eof;
    udp.strm.val = val;
  end

endmodule : udp_vlg_tx_ctl
