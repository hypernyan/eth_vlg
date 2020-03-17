import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

interface phy;
	logic       clk;
	logic [7:0] d;
	logic       v;
	logic       e;
	
	modport in  (input clk, d, v, e);
	modport out (output clk, d, v, e);
endinterface

interface mac;
	logic [7:0] d;
	logic       v;
	logic       err;
	logic       sof;
	logic       eof;
	logic       busy;
	mac_hdr_t   hdr;

	modport in  (input d, v, err, sof, eof, hdr, output busy);
	modport out (output d, v, err, sof, eof, hdr, input busy);
endinterface

module mac_vlg #(
	parameter TX_FIFO_SIZE = 8
)
(
	input   logic clk,
	input   logic rst,
	output  logic rst_fifo,
	input   dev_t dev,

	phy.in  phy_rx,
	phy.out phy_tx,

	mac.out rx,
	mac.in  tx,
	input  logic avl,
	output logic rdy
);

phy phy_rx_sync (.*);

mac_vlg_sync mac_vlg_sync_inst(.*);

mac_vlg_rx mac_vlg_rx_inst (
	.clk      (clk),
	.rst      (rst),
	.dev      (dev),
	.phy      (phy_rx),
	.mac      (rx)
);

mac_vlg_tx mac_vlg_tx_inst (
	.clk  (clk),
	.rst  (rst),
	.rst_fifo (rst_fifo),
	.dev  (dev),
	.phy  (phy_tx),
	.mac  (tx),

	.avl (avl),
	.rdy (rdy)
);

endmodule

module mac_vlg_rx (
	input logic clk,
	input logic rst,
	phy.in      phy,
	mac.out     mac,
	input dev_t dev
);
localparam HDR_LEN = 22;
fsm_t fsm;

logic fsm_rst;

logic [7:0] byte_cnt;

logic fcs_detected;
logic crc_ok;
logic crc_en;

logic       mac_v;
logic [7:0] mac_d;
logic       mac_sof;
logic       mac_eof;
logic       mac_err;
mac_hdr_t   mac_hdr;

logic [4:0][7:0] rxd_delay;
logic [1:0]      rxv_delay;

logic error;
logic receiving;

assign mac_v = mac.v;
assign mac_d = mac.d;

assign mac_sof = mac.sof;
assign mac_eof = mac.eof;
assign mac_err = mac.err;
assign mac_hdr = mac.hdr;

logic [7:0] hdr [HDR_LEN-1:0];

crc32 crc32_inst(
	.clk (clk),
	.rst (fsm_rst),
	.d   (phy.d),
	.v   (crc_en),
	.ok  (fcs_detected),
	.crc ()
);

always @ (posedge clk) begin
	if (fsm_rst) begin
		byte_cnt  <= 0;
		crc_en    <= 0;
		mac.hdr   <= '0;
		mac.v     <= 0;
		mac.sof   <= 0;
		receiving <= 0;
		error     <= 0;
	end
	else begin
		mac.sof <= (byte_cnt == 27);	
		if (phy.v) begin // Write to header and shift it 
			hdr[0] <= rxd_delay[4];
			hdr[HDR_LEN-1:1] <= hdr[HDR_LEN-2:0]; 
			byte_cnt <= byte_cnt + 1;
		end
		if (fcs_detected) begin
			mac.hdr.length <= byte_cnt; // Latch length
		end
		if (!rxv_delay[0] && phy.v) receiving <= 1;
		if (byte_cnt == 7) crc_en <= 1;
		if (byte_cnt == 27) begin
			mac.v <= 1;
			mac.hdr.ethertype    <= {hdr[1],  hdr[0]};
			mac.hdr.src_mac_addr <= {hdr[7],  hdr[6],  hdr[5],  hdr[4],  hdr[3], hdr[2]};
			mac.hdr.dst_mac_addr <= {hdr[13], hdr[12], hdr[11], hdr[10], hdr[9], hdr[8]};
		end

	end
end

always @ (posedge clk) begin
	rxd_delay[4:0] <= {rxd_delay[3:0], phy.d};
	rxv_delay[1:0] <= {rxv_delay[0], phy.v};
	fsm_rst <= (fcs_detected || mac.err || rst);

	mac.d <= rxd_delay[4];
	mac.err = (!phy.v && rxv_delay[0] && !fcs_detected);
	mac.eof <= fcs_detected;
end

endmodule : mac_vlg_rx

module mac_vlg_tx (
	input logic clk,
	input logic rst,
	output logic rst_fifo,

	phy.out phy,
	mac.in  mac,

	input  logic avl,
	output logic rdy,
	input  dev_t dev
);

localparam MIN_DATA_PORTION = 44;

// todo: remove fifo

fifo_sc_if #(8, 8) fifo(.*);
fifo_sc #(8, 8) fifo_inst(.*);

assign fifo.clk = clk;
assign fifo.rst = rst;

assign fifo.w_v = mac.v;
assign fifo.w_d = mac.d;

fsm_t fsm;

logic fsm_rst;
logic done;
logic pad_ok;

mac_hdr_t cur_hdr;
dev_t     cur_dev;

logic [2:0] preamble_byte_cnt;
logic [2:0] dst_byte_cnt;
logic [2:0] src_byte_cnt;
logic [1:0] tag_byte_cnt;
logic [0:0] ethertype_byte_cnt;
logic [2:0] fcs_byte_cnt;

logic [5:0] byte_cnt;

logic [31:0] crc_inv;
logic [31:0] crc;
logic [31:0] cur_fcs;
logic        crc_en;
logic  [7:0] d_hdr;
logic  [7:0] d_fcs;
logic  [7:0] d_hdr_delay;

assign crc = ~crc_inv;

assign rst_fifo = fsm_rst;

crc32 crc32_inst(
	.clk (clk),
	.rst (rst),
	.d   (d_hdr),
	.v   (crc_en),
	.ok  (),
	.crc (crc_inv)
);

assign mac.busy = rdy;

always @ (posedge clk) begin
	if (fsm_rst) begin
		fsm <= idle_s;
		preamble_byte_cnt  <= 0;
		dst_byte_cnt       <= 0;
		src_byte_cnt       <= 0;
		tag_byte_cnt       <= 0;
		ethertype_byte_cnt <= 0;
		fcs_byte_cnt       <= 0;
		byte_cnt           <= 0;
		rdy                <= 0;
		crc_en             <= 0;
		d_hdr              <= 0;
		phy.v              <= 0;
		done               <= 0;
		pad_ok             <= 0;
		fifo.r_v           <= 0;
	end
	else begin
		case (fsm)
			idle_s : begin
				if (avl) rdy <= 1;
				if (rdy) begin
					fsm <= pre_s;
					d_hdr <= 8'h55;
					cur_hdr.src_mac_addr <= dev.mac_addr;
					cur_hdr.dst_mac_addr <= mac.hdr.dst_mac_addr;
					cur_hdr.ethertype    <= mac.hdr.ethertype;					
					cur_dev <= dev;
				end
			end
			pre_s : begin
				phy.v <= 1;
				preamble_byte_cnt <= preamble_byte_cnt + 1;
				if (preamble_byte_cnt == 6) begin
					d_hdr <= 8'hd5;
					fsm <= dst_s;
				end
			end
			dst_s : begin
				crc_en <= 1;
				dst_byte_cnt <= dst_byte_cnt + 1;
				d_hdr <= cur_hdr.dst_mac_addr[5];
				cur_hdr.dst_mac_addr[5:1] <= cur_hdr.dst_mac_addr[4:0];
				if (dst_byte_cnt == 5) fsm <= src_s;
			end
			src_s : begin
				src_byte_cnt <= src_byte_cnt + 1;
				d_hdr <= cur_dev.mac_addr[5];
				cur_dev.mac_addr[5:1] <= cur_dev.mac_addr[4:0];
				if (src_byte_cnt == 5) fsm <= type_s;				
			end
			qtag_s : begin
				// Not supported currently
			end
			type_s : begin
				ethertype_byte_cnt <= ethertype_byte_cnt + 1;
				d_hdr <= cur_hdr.ethertype[1];
				cur_hdr.ethertype[1] <= cur_hdr.ethertype[0];
				fifo.r_v <= 1;
				if (ethertype_byte_cnt == 1) begin
					fsm <= payload_s;
					rdy <= 1;
				end
			end
			payload_s : begin
				byte_cnt <= byte_cnt + 1;
				rdy <= 0;
				d_hdr <= fifo.r_q;
				if (byte_cnt == MIN_DATA_PORTION) pad_ok <= 1;
				if (fifo.e && pad_ok) begin
					fsm <= fcs_s;
				end
			end
			fcs_s : begin
				crc_en <= 0;
				fcs_byte_cnt <= fcs_byte_cnt + 1;
				cur_fcs <= (fcs_byte_cnt == 1) ? {crc[7:0], crc[15:8], crc[23:16], crc[31:24]} : cur_fcs << 8;
				if (fcs_byte_cnt == 4) begin
					//$display("<- srv: Eth from %h:%h:%h:%h:%h:%h to %h:%h:%h:%h:%h:%h. Ethertype: %h",
					//	dev.mac_addr[5],
					//	dev.mac_addr[4],
					//	dev.mac_addr[3],
					//	dev.mac_addr[2],
					//	dev.mac_addr[1],
					//	dev.mac_addr[0],   
					//	mac.hdr.dst_mac_addr[5],
					//	mac.hdr.dst_mac_addr[4],
					//	mac.hdr.dst_mac_addr[3],
					//	mac.hdr.dst_mac_addr[2],
					//	mac.hdr.dst_mac_addr[1],
					//	mac.hdr.dst_mac_addr[0],
					//	mac.hdr.ethertype
					//);
					done <= 1;
				end
			end
		endcase
	end
end

logic [7:0] fifo_r_q;
logic fifo_e;

assign fifo_r_q = fifo.r_q;
assign fifo_e = fifo.e;

assign fsm_rst = (rst || done);

assign d_fcs = cur_fcs[31-:8];

always @ (posedge clk) d_hdr_delay <= d_hdr;

assign phy.d = (fcs_byte_cnt == 0 || fcs_byte_cnt == 1) ? d_hdr_delay : d_fcs;

endmodule : mac_vlg_tx
