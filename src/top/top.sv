
module top (
	input wire  clk_25m,


	// 
	// ETH
	// 
	(* chip_pin = "J22" *) output wire       phy_gtx_clk,
	(* chip_pin = "D22" *) input  wire       phy_rx_clk, 

	(* chip_pin = "W22" *) output wire       phy_tx_err, 
	(* chip_pin = "M21" *) output wire       phy_tx_val, 
	(* chip_pin = "W21, V22, V21, U22, R22, R21, P22, M22" *) output wire [7:0] phy_tx_dat, 

	(* chip_pin = "H21" *) input  wire       phy_rx_err, 
	(* chip_pin = "B21" *) input  wire       phy_rx_val,
	(* chip_pin = "F22, F21, E22, E21, D21, C22, C21, B22" *) input  wire [7:0] phy_rx_dat,

	(* chip_pin = "Y21" *) output wire       mdc,
	(* chip_pin = "Y22" *) output wire       mdio,

	(* chip_pin = "P3" *) output wire        reset_n,
	(* chip_pin = "P21" *) output wire       phy_rst_n
);

assign phy_rst_n = 1;

logic [7:0] tcp_din, tcp_dout;
logic tcp_vin, tcp_vout;

phy phy_rx(.*);
phy phy_tx(.*);

udp udp_rx(.*);
udp udp_tx(.*);

assign phy_rx.d = phy_rx_dat;
assign phy_rx.v = phy_rx_val;
assign phy_rx.e = phy_rx_err;

assign phy_tx_dat  = phy_tx.d;
assign phy_tx_val  = phy_tx.v;
assign phy_tx_err  = phy_tx.e;
assign phy_gtx_clk = phy_rx_clk;

logic rst;
eth_vlg #(
	.MAC_ADDR  (48'h107b444fd012),
	.IPV4_ADDR (32'hc0a800d5)
) eth_vlg_inst
(
	.phy_rx (phy_rx),
	.phy_tx (phy_tx),

	.clk (phy_rx_clk),
	.rst(1'b0),

	.udp_tx (udp_tx),
	.udp_rx (udp_rx),

	.tcp_din (tcp_din),
	.tcp_vin (tcp_vin),
	.tcp_cts (tcp_cts), // cts may go low after vin is aseerted. ignore it. do not assert vin to more then MTU ticks, then check for cts again

	.tcp_dout (),
	.tcp_vout (),
	// 'server'
	.connected (connected), 
	.listen    (1'b1), // 
	// 'client'
	.connect   (0), //!connected && (ctr == 12500000)), 
	.rem_ipv4  (32'hc0a800ea), // remote ipv4
	.rem_port  (1000) // remote port
);

logic [$clog2(20000)-1:0] ctr;
logic [15:0] tx_ctr;

enum logic {
	idle_s,
	tx_s
} fsm;
// generate ramp
always @ (posedge phy_rx_clk) begin
	if (rst) begin
		ctr <= 0;
		tx_ctr <= 0;
		tcp_vin <= 0;
		tcp_din <= 0;
		fsm <= idle_s;
	end
	else begin
		case (fsm)
			idle_s : begin
				ctr <= (ctr == 3000) ? ctr : ctr + 1;
				if (ctr == 3000 && tcp_cts) fsm <= tx_s;
				tcp_vin <= 0;
				tx_ctr <= 0;
			end
			tx_s : begin
				ctr <= 0;
				tx_ctr <= tx_ctr + 1;
				if (tx_ctr == 2000) fsm <= idle_s;
				tcp_vin <= 1;
				tcp_din <= tcp_din + 1;
			end
		endcase
	end
end

endmodule
