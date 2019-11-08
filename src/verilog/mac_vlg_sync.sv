module mac_vlg_sync #(
	parameter SIZE = 8
)
(
	input logic clk,
	input logic rst,
	phy.in      phy_rx,
	phy.out     phy_rx_sync
);

phy phy_delay(.*);
phy phy_delay1(.*);

phy phy_rx_sync_rx(.*);

fifo_dc_if #(SIZE,10) fifo (.*);
fifo_dc #(SIZE,10) fifo_dc_inst (.*);
//
assign fifo.rst   = rst;
assign fifo.clk_r = clk;
assign fifo.clk_w = phy_rx.clk;
////
assign fifo.v_w = phy_rx.v && !fifo.f_w;
assign fifo.d_w = phy_rx.d;
////
logic fifo_v_r;
assign fifo.v_r = fifo_v_r && !fifo.e_r;
//
always @ (posedge clk) begin
	fifo_v_r <= !fifo.e_r;
	phy_rx_sync.v <= fifo.v_r;
end

assign phy_rx_sync.d = fifo.q_r;
assign phy_rx_sync.clk = clk;


//always @ (posedge phy_rx.clk) begin
//	phy_rx_sync_rx.v <= phy_rx.v;
//	phy_rx_sync_rx.d <= phy_rx.d;
//	phy_rx_sync_rx.e <= phy_rx.e;
//end
//
//always @ (posedge clk) begin
//	phy_rx_sync.v <= phy_delay.v;
//	phy_rx_sync.d <= phy_delay.d;
//	phy_rx_sync.e <= phy_delay.e;
//
//	phy_delay.v <= phy_delay1.v;
//	phy_delay.d <= phy_delay1.d;
//	phy_delay.e <= phy_delay1.e;
//	
//	phy_delay1.v <= phy_rx_sync_rx.v;
//	phy_delay1.d <= phy_rx_sync_rx.d;
//	phy_delay1.e <= phy_rx_sync_rx.e;
//end
//

endmodule
