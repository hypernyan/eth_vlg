import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

interface phy;
  logic       clk;
  logic       rst;
  logic [7:0] dat;
  logic       val;
  logic       err;
  
  modport in  (input  clk, rst, dat, val, err);
  modport out (output clk, rst, dat, val, err);
endinterface

interface mac;
  logic [7:0] dat;
  logic       val;
  logic       err;
  logic       sof;
  logic       eof;
  logic       rdy;   // Ready to accept data for transmission
  logic       req;   // Request payload from logic that issued 'start'
  mac_meta_t  meta;   // MAC header

  modport in_rx  (input  dat, val, err, sof, eof, meta);
  modport out_rx (output dat, val, err, sof, eof, meta);
  modport in_tx  (input  dat, val,      sof, eof, meta, rdy, output req);
  modport out_tx (output dat, val,      sof, eof, meta, rdy, input  req);
endinterface

module mac_vlg #(
  parameter int TX_FIFO_SIZE = 8,
  parameter int CDC_FIFO_DEPTH = 8,
  parameter int CDC_DELAY = 4,
  parameter bit VERBOSE = 1
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,
  phy.in      phy_rx,
  phy.out     phy_tx,
  mac.out_rx  rx,
  mac.in_tx   tx
);

  phy phy_rx_sync (.*);
  
  // Syncronyze 125MHz phy_rx_clk
  // to local 125 MHz clock
  // Delay reading for a few ticks
  // in order to avoid packet rip
  // which may be caused by
  // incoherency of rx and local clocks
  
  mac_vlg_cdc #(  
    .FIFO_DEPTH (CDC_FIFO_DEPTH),
    .DELAY      (CDC_DELAY)
  ) mac_vlg_cdc_inst (
    // phy_rx_clk domain
    .clk_in     (phy_rx.clk),      // in
    .rst_in     (phy_rx.rst),      // in
    .data_in    (phy_rx.dat),      // in
    .valid_in   (phy_rx.val),      // in
    .error_in   (phy_rx.err),      // in
    // local clock domain
    .clk_out    (clk),             // in 
    .rst_out    (rst),             // in 
    .data_out   (phy_rx_sync.dat), // out
    .valid_out  (phy_rx_sync.val), // out
    .error_out  (phy_rx_sync.err)  // out
  );
  
  mac_vlg_rx #(
    .VERBOSE (VERBOSE)
  ) mac_vlg_rx_inst (
    .clk      (clk),
    .rst      (rst),
    .dev      (dev),
    .phy      (phy_rx_sync),
    .mac      (rx)
  );
  
  mac_vlg_tx #(
    .VERBOSE (VERBOSE)
  ) mac_vlg_tx_inst (
    .clk      (clk),
    .rst      (rst),
    .dev      (dev),
    .phy      (phy_tx),
    .mac      (tx)
  );

endmodule

module mac_vlg_rx #(
  parameter bit VERBOSE = 1
)(
  input logic clk,
  input logic rst,
  phy.in      phy,
  mac.out_rx  mac,
  input dev_t dev
);

logic fsm_rst;

logic [15:0] byte_cnt;

logic fcs_detected;
logic crc_en;

logic [4:0][7:0] rxd_delay;
logic [1:0]      rxv_delay;

logic error;
logic receiving;

logic [7:0] hdr [MAC_HDR_LEN-1:0];

crc32 crc32_inst(
  .clk (clk),
  .rst (fsm_rst),
  .dat (phy.dat),
  .val (crc_en),
  .ok  (fcs_detected),
  .crc ()
);

always @ (posedge clk) begin
  if (fsm_rst) begin
    byte_cnt     <= 0;
    crc_en       <= 0;
    mac.meta.hdr <= '0;
    mac.val      <= 0;
    mac.sof      <= 0;
    receiving    <= 0;
    error        <= 0;
  end
  else begin
    mac.sof <= (byte_cnt == 27);  
    if (phy.val) begin // Write to header and shift it 
      hdr[0] <= rxd_delay[4];
      hdr[MAC_HDR_LEN-1:1] <= hdr[MAC_HDR_LEN-2:0]; 
      byte_cnt <= byte_cnt + 1;
    end
    if (!rxv_delay[0] && phy.val) receiving <= 1;
    if (byte_cnt == 7) crc_en <= 1;
    if (byte_cnt == 27) begin
      mac.val <= 1;
      mac.meta.hdr.ethertype <= {hdr[1],  hdr[0]};
      mac.meta.hdr.src_mac <= {hdr[7],  hdr[6],  hdr[5],  hdr[4],  hdr[3], hdr[2]};
      mac.meta.hdr.dst_mac <= {hdr[13], hdr[12], hdr[11], hdr[10], hdr[9], hdr[8]};
    end
  end
end

always @ (posedge clk) begin
  rxd_delay[4:0] <= {rxd_delay[3:0], phy.dat};
  rxv_delay[1:0] <= {rxv_delay[0], phy.val};
  fsm_rst <= (fcs_detected || mac.err || rst);

  mac.dat <= rxd_delay[4];
  mac.err = (!phy.val && rxv_delay[0] && !fcs_detected);
  mac.eof <= fcs_detected;
end

endmodule : mac_vlg_rx

module mac_vlg_tx #(
  parameter bit VERBOSE = 1
)(
  input logic  clk,
  input logic  rst,
  input  dev_t dev,
  phy.out      phy,
  mac.in_tx    mac
);

  localparam MIN_DATA_PORTION = 44;
  assign phy.clk = clk;
  
  logic fsm_rst;
  logic done;
  logic pad_ok;
  
  logic [3:0][7:0] crc_inv;
  logic [3:0][7:0] crc;
  logic [3:0][7:0] cur_fcs;
  logic        crc_en;
  logic  [7:0] dat, dat_reg;
  
  assign crc = ~crc_inv;
  
  crc32 crc32_inst(
    .clk (clk),
    .rst (rst),
    .dat (dat),
    .val (crc_en),
    .ok  (),
    .crc (crc_inv)
  );

  enum logic [3:0] {
    idle_s,
    hdr_s,
    payload_s,
    fcs_s
  } fsm;
  
  length_t cur_len, byte_cnt;
  
  logic [MAC_HDR_LEN-1:0] [7:0] cur_hdr;
  logic [$clog2(MAC_HDR_LEN+1)-1:0] hdr_byte_cnt;
  logic fcs, val;
  logic [1:0] fcs_byte_cnt;
  always @ (posedge clk) begin
    if (fsm_rst) begin
      fsm            <= idle_s;
      fcs_byte_cnt   <= 0;
      byte_cnt       <= 0;
      mac.req        <= 0;
      crc_en         <= 0;
      val            <= 0;
      done           <= 0;
      pad_ok         <= 0;
      cur_len        <= 0;
      cur_hdr        <= 0;
      hdr_byte_cnt   <= 0;
      fcs <= 0;
      cur_fcs <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (mac.rdy) begin // 
            fsm <= hdr_s;
            cur_len <= mac.meta.len;
            $display("transmitting. dst mac: %h", mac.meta.hdr.dst_mac);
            $display("transmitting. src mac: %h", mac.meta.hdr.src_mac);
            cur_hdr <= {PREAMBLE, mac.meta.hdr.dst_mac, dev.mac_addr, mac.meta.hdr.ethertype};
          end
        end
        hdr_s : begin
          if (hdr_byte_cnt == 8) crc_en <= 1;
          val <= 1;
          dat <= cur_hdr[MAC_HDR_LEN-1];
          cur_hdr[MAC_HDR_LEN-1:1] <= cur_hdr[MAC_HDR_LEN-2:0];
          hdr_byte_cnt <= hdr_byte_cnt + 1;
          if (hdr_byte_cnt == MAC_HDR_LEN-5) mac.req <= 1;
          if (hdr_byte_cnt == MAC_HDR_LEN-1) begin
            fsm <= payload_s;
          end
        end
        payload_s : begin
          dat <= mac.dat;
          byte_cnt <= byte_cnt + 1;
          if (byte_cnt == MIN_DATA_PORTION) pad_ok <= 1;
          if (byte_cnt == cur_len - 1) begin
            fsm <= fcs_s;
          end
        end
        fcs_s : begin
          fcs <= 1;
        //  if (fcs_byte_cnt == 0) cur_fcs <= {crc[7:0], crc[15:8], crc[23:16], crc[31:24]};
        //  phy.dat <= 
        //  crc_en <= 0;
          fcs_byte_cnt <= fcs_byte_cnt + 1;
          cur_fcs <= (fcs_byte_cnt == 1) ? crc : cur_fcs >> 8;
           if (fcs_byte_cnt == 3) begin
            if (VERBOSE) $display("[DUT]-> Frame from %h:%h:%h:%h:%h:%h to %h:%h:%h:%h:%h:%h. Ethertype: %h",
              dev.mac_addr[5],
              dev.mac_addr[4],
              dev.mac_addr[3],
              dev.mac_addr[2],
              dev.mac_addr[1],
              dev.mac_addr[0],   
              mac.meta.hdr.dst_mac[5],
              mac.meta.hdr.dst_mac[4],
              mac.meta.hdr.dst_mac[3],
              mac.meta.hdr.dst_mac[2],
              mac.meta.hdr.dst_mac[1],
              mac.meta.hdr.dst_mac[0],
              mac.meta.hdr.ethertype
            );
            done <= 1;
          end
        end
      endcase
    end
  end

  assign fsm_rst = (rst || done);
  
  always @ (posedge clk) dat_reg <= dat;
  assign phy.val = val;
  assign phy.dat = fcs ? (fcs_byte_cnt == 1) ? crc[0] : cur_fcs[1] : dat;
 // assign phy.dat = (fcs_byte_cnt == 0 || fcs_byte_cnt == 1) ? cur_hdr[MAC_HDR_LEN-1:1] : d_fcs;

endmodule : mac_vlg_tx

module mac_vlg_cdc #(
  parameter FIFO_DEPTH = 8, // The value should be reasonable for the tool to implement DP RAM
  parameter DELAY = 4 
)(
  input  logic       clk_in,
  input  logic       rst_in,
  input  logic [7:0] data_in,
  input  logic       valid_in,
  input  logic       error_in,

  input  logic       clk_out,
  input  logic       rst_out,
  output logic [7:0] data_out,
  output logic       valid_out,
  output logic       error_out
);

// Introduce a readout delay to make sure valid_out will have no interruptions 
// because rx_clk and clk are asynchronous 
logic [DELAY-1:0] empty;
fifo_dc_if #(FIFO_DEPTH, 8) fifo(.*);
fifo_dc    #(FIFO_DEPTH, 8) fifo_inst(.*);

assign fifo.clk_w = clk_in;
assign fifo.rst_w = rst_in;

assign fifo.data_in = data_in;
assign fifo.write = valid_in;

assign fifo.clk_r = clk_out;
assign fifo.rst_r = rst_out;

assign data_out  = fifo.data_out;
assign valid_out = fifo.valid_out;

always @ (posedge clk_out) begin
  empty[DELAY-1:0] <= {empty[DELAY-2:0], fifo.empty};
  fifo.read <= ~empty[DELAY-1];
end

endmodule
