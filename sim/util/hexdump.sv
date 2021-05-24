module hexdump #( 
	parameter FILENAME = "dump", 
	parameter OFFSET = 1,
	parameter VERBOSE = 1
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
  
  always_ff @ (posedge clk) vin_prev <= vin; 
  string num_str;

  initial begin 
 	  num = 0; 
  end 
 
  always_ff @ (posedge clk) begin 
    d_pipe[PIPE_LEN-1:0] <= {d_pipe[PIPE_LEN-2:0], din[7:0]}; 
  	v_pipe[PIPE_LEN-1:0] <= {v_pipe[PIPE_LEN-2:0],      vin}; 
  	if (vin_prev && !vin) begin 
  		pkt_num <= pkt_num + 1; 
  		packet_val <= (pkt_num == OFFSET - 1);  
  	end 
    if (!vin_prev && vin) begin
      num_str.itoa(pkt_num);
      f = $fopen({FILENAME, num_str, ".txt"}, "w");
      stop <= 0;
    end
  	if (vin) begin 
  		if (byte_cnt > 7 && !stop) $fwrite(f, "%h\n", din);
  		byte_cnt <= byte_cnt + 1; 
  	end 
  	else if (vin_prev && !vin) begin
      if (VERBOSE) $display("Dumped file %s", {FILENAME, num_str, ".txt"});
      $fclose(f);
      pkt_num <= pkt_num + 1;
  		stop <= 1;
      byte_cnt <= 0;
  	end 
  end 
   
endmodule 
