
module timer #(
    parameter TICKS = 1000 
)
(
    input logic  clk,
    input logic  rst,
    input logic  i,
	output logic o
);

logic [$clog2(TICKS+1)-1:0] ctr;

always @ (posedge clk) begin
	if (rst) begin
		ctr <= 0;
		o <= 0;
	end
	else begin
		ctr <= (i) ? ctr + 1 : ctr;
		o <= (ctr == TICKS);
	end
end

endmodule

