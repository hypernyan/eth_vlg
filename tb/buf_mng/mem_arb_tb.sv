module mem_arb_tb ( );

localparam N = 3;
localparam W = 8;
localparam WIDTH = 10;

logic clk;
logic rst;

always #4 clk <= ~clk;

logic [N-1:0]         v_i;
logic [N-1:0] [W-1:0] d_i;
logic [N-1:0]         en;

logic v_o;
logic [W-1:0] d_o;
logic avl;
logic rdy;
logic [N-1:0] act_ms;
logic [N-1:0] avl_v;
logic [N-1:0] cur;
logic emp;

logic eof;
buf_mng dut (.*);

defparam dut.N = 3;
defparam dut.D = {N{WIDTH}};
defparam dut.W = 8;

initial begin
	rst        <= 1;
	clk        <= 0;
	rdy        <= 0;
	v_i[N-1:0] <= '0;
	d_i[N-1:0] <= '0;
#100
	rst <= 0;
#100
	en[0] <= 1;
#100
	en[1] <= 1;
#200
	en[2] <= 1;
#100
	en[0] <= 0;
#300
	en[1] <= 0;
	en[2] <= 0;
#100
	rdy <= 1;
#9
	rdy <= 0;
#1000
	rdy <= 1;
#9
	rdy <= 0;
#1000
	rdy <= 1;
#9
	rdy <= 0;

end

always @ (posedge clk) begin
	if (rst) begin
		v_i[N-1:0] <= '0;
		d_i[N-1:0] <= '0;
	end
	else begin
		for (int i = 0; i < N; i++) begin
			if (en[i]) begin
				v_i[i] <= 1;
				d_i[i] <= d_i[i] + 1;
			end
			else v_i[i] <= 0;
		end
	end
end

endmodule