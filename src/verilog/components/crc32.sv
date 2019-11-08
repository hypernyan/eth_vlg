import mac_vlg_pkg::*;
//`define SIMULATION
module crc32 (
	input  logic        clk,
	input  logic        rst,
	input  logic [7:0]  d,
	input  logic        v,
	output logic        ok,
	output logic [31:0] crc
);

localparam [31:0] CRC_POLY         = 32'hEDB88320;
//localparam [31:0] CRC_POLY         = 32'h04C11DB7;
localparam [31:0] CRC_MAGIC_NUMBER = 32'hDEBB20E3;
int i, j;
bit [31:0] cur;
int f;

logic [31:0] crc_table [255:0];

initial begin
`ifdef SIMULATION
  f = $fopen("crc_table.txt", "w");
  for (i = 0; i < 256; i = i+1) begin
    cur = i;
	for (j = 0; j < 8; j = j+1) begin
	  cur = (cur[0] && 1'b1) ? (cur >> 1) ^ CRC_POLY : cur >> 1; 
    end
    $fwrite(f,"%h\n",cur);
  end
  $fclose(f);
`endif // SIMULATION
  $readmemh("crc_table.txt", crc_table);
end

logic [31:0] crc_del;
logic [31:0] crc_table_q;
logic v_del;

always @ (posedge clk) begin
	if (rst) begin
		v_del       <= 0;
		crc_del     <= 0;
	end
	else begin
		v_del <= v;
		crc_del <= crc;
		crc_table_q <= crc_table[(crc[7:0] ^ d[7:0]) & 8'hff];
	end
end

assign crc = (v_del) ? crc_table_q ^ (crc_del >> 8) : '1; 
assign ok = (crc == CRC_MAGIC_NUMBER);

endmodule
