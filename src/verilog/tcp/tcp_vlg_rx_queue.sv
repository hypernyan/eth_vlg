
import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

module tcp_vlg_rx_queue (
	input logic clk,
	input logic rst,
	input dev_t dev,
	// 
	
	tcp.in tcp,
	input tcb_t tcb,
	output tcp_ack_num_t cur_ack,
	output logic [7:0] dout,
	output logic vout,
	input logic connected
);

logic connected_prev;
logic [15:0] cur_byte_ctr;


always @ (posedge clk) begin
	connected_prev <= connected;
	if (!connected_prev && connected) cur_ack <= tcb.rem_ack_num;
	else if (tcp.tcp_hdr_v && tcb.loc_ack_num == tcp.tcp_hdr.tcp_seq_num - 1) begin
		cur_ack <= tcp.tcp_hdr.tcp_seq_num + tcp.ipv4_hdr.length;
		cur_byte_ctr <= tcp.ipv4_hdr.length;
	end
	else if (cur_byte_ctr != 0) begin
		vout <= 1;
		dout <= tcp.d;
		cur_byte_ctr <= cur_byte_ctr - 1;
	end
	else vout <= 0;
end

endmodule : tcp_vlg_rx_queue
