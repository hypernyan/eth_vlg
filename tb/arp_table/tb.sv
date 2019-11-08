import arp_vlg_pkg::*;
import mac_vlg_pkg::*;
import ip_vlg_pkg::*;
import eth_vlg_pkg::*;


module tb ( );


localparam N = 3;
localparam W = 8;
localparam WIDTH = 10;

logic clk;
logic rst;

always #1 clk <= ~clk;

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


logic [79:0] arp_entry_list [0:7];

arp_data arp_data_in  (.*);
arp_data arp_data_out (.*);

initial begin
	arp_entry_list[0] = {8'd192, 8'd168, 8'd0, 8'd2, 8'hde, 8'had, 8'hbe, 8'hef, 8'h00, 8'h20};
	arp_entry_list[1] = {8'd192, 8'd168, 8'd0, 8'd3, 8'hde, 8'had, 8'hbe, 8'hef, 8'h00, 8'h21};
	arp_entry_list[2] = {8'd192, 8'd168, 8'd0, 8'd4, 8'hde, 8'had, 8'hbe, 8'hef, 8'h00, 8'h22};
	arp_entry_list[3] = {8'd192, 8'd168, 8'd0, 8'd1, 8'hde, 8'had, 8'hbe, 8'hef, 8'h00, 8'h23};
	arp_entry_list[4] = {8'd192, 8'd168, 8'd0, 8'd2, 8'hde, 8'had, 8'hbe, 8'hef, 8'h00, 8'h24};
	arp_entry_list[5] = {8'd192, 8'd168, 8'd0, 8'd1, 8'hde, 8'had, 8'hbe, 8'hef, 8'h00, 8'h25};
	arp_entry_list[6] = {8'd192, 8'd168, 8'd0, 8'd9, 8'hde, 8'had, 8'hbe, 8'hef, 8'h00, 8'h26};
	arp_entry_list[7] = {8'd192, 8'd168, 8'd0, 8'd7, 8'hde, 8'had, 8'hbe, 8'hef, 8'h00, 8'h27};
end

logic req;
ipv4_t req_ipv4_addr;
ipv4_t arp_req_ipv4_addr;
logic arp_req;
logic rsp_err;
arp_table #(
    .ARP_TABLE_SIZE (8)
) dut (
    .clk           (clk),
    .rst           (rst),

    .arp_in        (arp_data_in),
	.arp_out       (arp_data_out),
	.rsp_err       (rsp_err),
    .req           (req),
    .req_ipv4_addr (req_ipv4_addr),
	.arp_req           (arp_req),
    .arp_req_ipv4_addr (arp_req_ipv4_addr)
);

ipv4_t     arp_data_in_ipv4_addr;
mac_addr_t arp_data_in_mac_addr;
logic      arp_data_in_val;

assign arp_data_in_ipv4_addr  = arp_data_in.ipv4_addr;
assign arp_data_in_mac_addr   = arp_data_in.mac_addr;
assign arp_data_in_val        = arp_data_in.val;

initial begin
	rst <= 1;
	clk <= 0;
	#200
	rst <= 0;
	arp_data_in.ipv4_addr = arp_entry_list[0][79:48];
	arp_data_in.mac_addr  = arp_entry_list[0][47:0];
	arp_data_in.val = 1;
	#2
	arp_data_in.val = 0;
	#10
	arp_data_in.ipv4_addr = arp_entry_list[1][79:48];
	arp_data_in.mac_addr  = arp_entry_list[1][47:0];
	arp_data_in.val = 1;
	#2
	arp_data_in.val = 0;	
	#10
	arp_data_in.ipv4_addr = arp_entry_list[2][79:48];
	arp_data_in.mac_addr  = arp_entry_list[2][47:0];
	arp_data_in.val = 1;
	#2
	arp_data_in.val = 0;	
	#10
	arp_data_in.ipv4_addr = arp_entry_list[3][79:48];
	arp_data_in.mac_addr  = arp_entry_list[3][47:0];
	arp_data_in.val = 1;
	#2
	arp_data_in.val = 0;	
	#10
	arp_data_in.ipv4_addr = arp_entry_list[4][79:48];
	arp_data_in.mac_addr  = arp_entry_list[4][47:0];
	arp_data_in.val = 1;
	#2
	arp_data_in.val = 0;	
	#10
	arp_data_in.ipv4_addr = arp_entry_list[5][79:48];
	arp_data_in.mac_addr  = arp_entry_list[5][47:0];
	arp_data_in.val = 1;
	#2
	arp_data_in.val = 0;	
	#10
	arp_data_in.ipv4_addr = arp_entry_list[6][79:48];
	arp_data_in.mac_addr  = arp_entry_list[6][47:0];
	arp_data_in.val = 1;
	#2
	arp_data_in.val = 0;	
	#100
	req_ipv4_addr <= {8'd192, 8'd168, 8'd0, 8'd2};
	req <= 1;
	#2
	req <= 0;
	#1000000
	req_ipv4_addr <= {8'd192, 8'd168, 8'd0, 8'd2};
	req <= 1;
	#2
	req <= 0;
end

endmodule