module hexdump #(
	parameter FILENAME = "dump.txt",
	parameter OFFSET = 4
)
(
	input logic       clk,
	input logic       vin,
	input logic [7:0] din
);

localparam int PIPE_LEN = 4;

int f = 0; 
int num = 0; 
int pkt_num = 0;
logic vin_prev = 0;
logic packet_val = 0;
int byte_cnt = 0;
logic stop = 0;
logic [PIPE_LEN-1:0][7:0] d_pipe = 0;
logic [PIPE_LEN-1:0] v_pipe = 0;

always @ (posedge clk) vin_prev <= vin;

initial begin
	f = $fopen(FILENAME, "w");
	num = 0;
end

always @ (posedge clk) begin
	if (vin_prev && !vin) begin
		pkt_num <= pkt_num + 1;
		packet_val <= (pkt_num == OFFSET - 1); 
	end
	if (packet_val) begin
		d_pipe[PIPE_LEN-1:0] <= {d_pipe[PIPE_LEN-2:0], din[7:0]};
		v_pipe[PIPE_LEN-1:0] <= {v_pipe[PIPE_LEN-2:0],      vin};
		if (vin) begin
			if (byte_cnt > 11 && vin && !stop) $fwrite(f, "%h\n", d_pipe[PIPE_LEN-1]);
			byte_cnt <= byte_cnt + 1;
		end
		else if (vin_prev && !vin) begin
			stop <= 1;
		end
	end
end

endmodule
