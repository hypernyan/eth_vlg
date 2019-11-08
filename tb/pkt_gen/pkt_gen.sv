import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;

import eth_vlg_pkg::*;

module pkt_gen (
	input logic       clk,
	input logic       rst,
	input dev_t       local_dev, // local device (pkt_gen simulation hdl)
	input ipv4_t      srv_ipv4_addr, // server's ipv4 and port. note that server's MAC is not known before ARP
	input port_t      srv_udp_port,

	phy.out           phy_tx, // 8-bit interface to server
	phy.in            phy_rx // ... from server. can be used as GMII interface.
);

localparam string PING_FILE = "../../sample_packets/packet3.txt";

localparam int
MAC_HDR_LEN  = 26,
ICMP_HDR_LEN = 8,
IPV4_HDR_LEN = 20,
TCP_HDR_LEN  = 20;

localparam int MTU = 1600;

mac_hdr_t mac_hdr;

class pkt_gen_c;
	////////////////
	// Common t&f //
	////////////////
	task automatic read_file;
		input string file;
		output int   len;
		output logic [7:0] pkt [0:MTU-1];
		int ctr = 0;
		int f;
		for (int i = 0; i < MTU; i++) pkt[i] = 8'hxx;
		begin
		//	$display("*** PKT GEN *** Reading file %s", file);
			$readmemh(file, pkt);
			while (pkt[ctr] !== 8'hxx) ctr = ctr + 1;
			len = ctr;
			for (int j = ctr; j < MTU; j++) pkt[j] = 0;
		//	$display("*** PKT GEN *** Done reading. Packet length: %d", len);
		end
	endtask : read_file

	function automatic [3:0][7:0] gen_crc;
		input [7:0] data [0:MTU-1];
		input int len;
		logic [31:0] CRC_POLY = 32'hEDB88320;	
		logic [31:0] crc_table [255:0];
		logic [31:0] crc = '1;
		for (int i = 0; i < 256; i = i+1) begin
	  		crc_table[i] = i;
			for (int j = 0; j < 8; j = j+1) crc_table[i] = (crc_table[i][0] && 1'b1) ? (crc_table[i] >> 1) ^ CRC_POLY : crc_table[i] >> 1;
		end
		for (int i = 0; i < len; i = i + 1) crc = crc_table[(crc[7:0]^data[i]) & 8'hff] ^ (crc >> 8);
		gen_crc = ~crc;
	endfunction : gen_crc

	task shift_data;
		ref [7:0] data [0:MTU-1];
		input int data_len;
		input int shift_len;
		for (int i = data_len+1; i > 0; i--) data[i+(shift_len-1)] = data[i-1];
	endtask : shift_data
	
	task automatic send_pkt;
		input [7:0] data [0:MTU-1]; // generated packet is stored here
		input int len;
		for (int i = 0; i < len + MAC_HDR_LEN; i++) begin
			@ (posedge clk) begin
				phy_tx.d <= data[i];
				phy_tx.v <= 1;
			end
		end	
		@ (posedge clk) begin
			phy_tx.v <= 0;
			phy_tx.d <= 0;
		end
	endtask : send_pkt

	task automatic compare;
		input [7:0] data_a [0:MTU-1];
		input [7:0] data_b [0:MTU-1];

		input int len;
		output bit equal;
		equal = 0;
		for (int i = 0; i < len; i++) if (data_a[i] != data_b[i]) disable compare;
		equal = 1;
	endtask : compare

	/////////////////////////
	// Send and wait tasks //
	/////////////////////////

	task arp_request;
		input ipv4_t ipv4_addr;
		output mac_addr_t mac_addr;
		input dev_t local_dev;
		output bit to;
		output bit bad_frame;

		logic [7:0] data_tx [0:MTU-1];
		logic [7:0] data_rx [0:MTU-1];

		int len_tx, len_rx;

		pkt_gen.gen_arp_pkt(ipv4_addr, local_dev, data_tx, len_tx, mac_hdr);
		pkt_gen.gen_eth_pkt(data_tx, len_tx, mac_hdr); // Generate mac packet
		pkt_gen.send_pkt(data_tx, len_tx);
		pkt_gen.receive_to(data_rx, to, len_rx, 1000);
		if (to) begin
			$display("xx cli: ARP request timeout.");
			disable arp_request;
		end
		else begin
			arp_parse(data_rx, len_rx, bad_frame, ipv4_addr, mac_addr);
		end
		//$display("ipv4_addr: %d:%d:%d:%d", ipv4_addr[3], ipv4_addr[2], ipv4_addr[1], ipv4_addr[0]); 
		//$display("mac: %h:%h:%h:%h:%h:%h", mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
		to = 0;
	endtask

	task ping;
		input string file;
		input dev_t local_dev;
		input dev_t remote_dev;

		logic [7:0] data_tx [0:MTU-1];
		logic [7:0] data_rx [0:MTU-1];
		logic [7:0] data_tx_raw [0:MTU-1];
		
		int len_rx;
		int len_tx;
		int len_tx_raw;

		bit to;
		bit bad_frame;
		bit equal;
		ipv4_t ipv4_addr; 
		mac_addr_t src_mac;
		mac_addr_t dst_mac;
		ipv4_hdr_t ipv4_hdr;
		mac_hdr_t  mac_hdr;

		read_file(file, len_tx, data_tx); // Read file, copy to 'data'
		if (len_tx < 18) begin
			$display("xx cli: ICMP packet too short.");
			disable ping;
		end
		data_tx_raw = data_tx; // Store raw ICMP data to compare with received
		len_tx_raw = len_tx;
		pkt_gen.gen_icmp_pkt(data_tx, len_tx, local_dev, remote_dev.ipv4_addr, ipv4_hdr); // Send ping to
		pkt_gen.gen_ipv4_pkt(data_tx, len_tx, ipv4_hdr,  remote_dev.mac_addr,  mac_hdr);
		pkt_gen.gen_eth_pkt(data_tx, len_tx, mac_hdr);
		pkt_gen.send_pkt(data_tx, len_tx);

		pkt_gen.receive_to(data_rx, to, len_rx, 1000);
		if (to) begin
			$display("xx cli: Ping timeout.");
			disable ping;
		end
		eth_parse (data_rx, len_rx, bad_frame, src_mac, dst_mac);
		ipv4_parse (data_rx, len_rx);
		icmp_parse (data_rx, len_rx, bad_frame);
		compare(data_rx, data_tx_raw, len_rx, equal);
		if (equal && (len_rx == len_tx_raw)) $display("-- cli: Ping OK."); else $display("xx cli: Ping error - bad reply. %d %d %d", len_rx, len_tx_raw, equal);
	endtask

	///////////////////////
	// Packet generators //
	///////////////////////

	task automatic gen_arp_pkt;
		// Ports
		input ipv4_t ipv4_addr;
		input dev_t  local_dev;
		output [7:0] data [0:MTU-1]; // generated packet is stored here
		output int len; // length of generated packet
		output mac_hdr_t mac_hdr; // header to generate mac frame
		// Task
		$display("<- cli: ARP request from %d.%d.%d.%d at %h:%h:%h:%h:%h:%h to %d.%d.%d.%d",
			local_dev.ipv4_addr[3],
			local_dev.ipv4_addr[2],
			local_dev.ipv4_addr[1],
			local_dev.ipv4_addr[0],
			local_dev.mac_addr[5],
			local_dev.mac_addr[4],
			local_dev.mac_addr[3],
			local_dev.mac_addr[2],
			local_dev.mac_addr[1],
			local_dev.mac_addr[0],
			ipv4_addr[3],
			ipv4_addr[2],
			ipv4_addr[1],
			ipv4_addr[0]
		);
		len = 46;
		data[0:27] = 
		{8'h0, 8'h1, 8'h08, 8'h00,
		 8'd6, 8'd4, 8'h0, 8'h1,
		 local_dev.mac_addr[5], local_dev.mac_addr[4], local_dev.mac_addr[3], local_dev.mac_addr[2], local_dev.mac_addr[1], local_dev.mac_addr[0],
		 local_dev.ipv4_addr[3], local_dev.ipv4_addr[2], local_dev.ipv4_addr[1], local_dev.ipv4_addr[0],
		 8'hff, 8'hff, 8'hff, 8'hff, 8'hff, 8'hff,
		 ipv4_addr[3], ipv4_addr[2], ipv4_addr[1], ipv4_addr[0]
		};
		// Padding 
		data[28:47] = {8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00};
		mac_hdr.ethertype = 16'h0806;
		mac_hdr.src_mac_addr = local_dev.mac_addr;
		mac_hdr.dst_mac_addr = 48'hffffffffffff;

	endtask : gen_arp_pkt

	// Generates ICMP packet of type 8 code 0 (ICMP request)
	task automatic gen_icmp_pkt;
		// ports
		ref [7:0]         data [0:MTU-1];
		ref   int         len;
		input dev_t       local_dev;
		input ipv4_t      ipv4_addr;
		output ipv4_hdr_t ipv4_hdr;
		$display("");

		// set IPv4 header
		ipv4_hdr.ver      = 4;
		ipv4_hdr.ihl      = 5;
		ipv4_hdr.qos      = 0;
		ipv4_hdr.length   = len + 20;
		ipv4_hdr.id       = $random();
		ipv4_hdr.zero = 0;
		ipv4_hdr.df       = 1;
		ipv4_hdr.mf       = 0;
		ipv4_hdr.fo       = 0;
		ipv4_hdr.ttl      = 128;
		ipv4_hdr.proto    = 1; // ICMP
		ipv4_hdr.src_ip   = local_dev.ipv4_addr;
		ipv4_hdr.dst_ip   = ipv4_addr;
		for (int i = len + 1; i > 0; i--) data[i+(ICMP_HDR_LEN-1)] = data[i-1]; // make space for ICMP header
		data[0] = 8; // echo request
		data[1] = 0; // code 0
		data[2:3] = {8'h00, 8'h00};
		data[4:7] = {8'h00, 8'h00, 8'h00, 8'h00};
		len = len + ICMP_HDR_LEN;
			$display("<- cli: ICMP packet from %d.%d.%d.%d to %d.%d.%d.%d",
				local_dev.ipv4_addr[3],
				local_dev.ipv4_addr[2],
				local_dev.ipv4_addr[1],
				local_dev.ipv4_addr[0],
				ipv4_addr[3],
				ipv4_addr[2],
				ipv4_addr[1],
				ipv4_addr[0]
			);
	endtask : gen_icmp_pkt

	task automatic gen_ipv4_pkt;
		ref [7:0] data [0:MTU-1];
		ref  int  len;
		input ipv4_hdr_t ipv4_hdr;
		input mac_addr_t mac_addr; // Destination MAC
		output mac_hdr_t mac_hdr;
		begin
			$display("<- cli: IPv4 packet from %d.%d.%d.%d to %d.%d.%d.%d",
				local_dev.ipv4_addr[3],
				local_dev.ipv4_addr[2],
				local_dev.ipv4_addr[1],
				local_dev.ipv4_addr[0],
				ipv4_hdr.dst_ip[3],
				ipv4_hdr.dst_ip[2],
				ipv4_hdr.dst_ip[1],
				ipv4_hdr.dst_ip[0]
			);
			len = len + 20;
			for (int i = len + 1; i > 0; i--) data[i+(IPV4_HDR_LEN-1)] = data[i-1];
			data[0] = 8'h45;
			data[1] = 0;
			data[2:3] = {len[15:8], len[7:0]};
			data[4:5] = {ipv4_hdr.id[1], ipv4_hdr.id[0]};
			data[6][7:5] = {ipv4_hdr.df, ipv4_hdr.mf, 1'b0};
			{data[6][4:0], data[7]} = ipv4_hdr.fo;
			data[8] = ipv4_hdr.ttl;
			data[9] = ipv4_hdr.proto;
			data[10:11] = {8'h0,8'h0};
			data[12:15] = {ipv4_hdr.src_ip[3], ipv4_hdr.src_ip[2], ipv4_hdr.src_ip[1], ipv4_hdr.src_ip[0]};
			data[16:19] = {ipv4_hdr.dst_ip[3], ipv4_hdr.dst_ip[2], ipv4_hdr.dst_ip[1], ipv4_hdr.dst_ip[0]};

			mac_hdr.ethertype = 16'h0800;
			mac_hdr.src_mac_addr = local_dev.mac_addr;
			mac_hdr.dst_mac_addr = mac_addr;
		end
	endtask : gen_ipv4_pkt

	// Reads 'data' and changes it according to mac header to be passed directly to phy
	task automatic gen_eth_pkt;
		// Ports
		ref [7:0] data [0:MTU-1];
		ref int len;
		input mac_hdr_t mac_hdr;
		// Task
		logic [3:0][7:0] crc;
		for (int i = len+1; i > 0; i--) data[i+13] = data[i-1]; // Make space for Ethernet header
		for (int i = 0; i < 6; i++) begin                       // Fill in header
			data[i]   = (mac_hdr.dst_mac_addr[5-i]);
			data[i+6] = (mac_hdr.src_mac_addr[5-i]);
		end
		data[12:13] = {mac_hdr.ethertype[1], mac_hdr.ethertype[0]};
		crc = gen_crc(data, len + 14); // calculate crc
		for (int i = 0; i < 4; i++) data[i+len+14] = crc[i]; // Append crc
		for (int i = len+1+22; i > 0; i--) data[i+7] = data[i-1]; // Make space for preamble
		data[0:7]  = {8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hd5};
	endtask : gen_eth_pkt

	////////////////////
	// Packet parsers //
	////////////////////

	// Parses ARP packet for sender's IPv4 and MAC
	task arp_parse;
		input [7:0] data [0:MTU-1];
		input int len;
		output bit bad_frame;
		output ipv4_t ipv4_addr; 
		output mac_addr_t mac_addr;  
		logic [7:0] eth_data [0:MTU-1];
		mac_addr_t src_mac, dst_mac;
		eth_parse (data, len, bad_frame, src_mac, dst_mac);
		ipv4_addr = {data[28], data[29], data[30], data[31]};
		mac_addr  = {data[22], data[23], data[24], data[25], data[26], data[27]};
		if (bad_frame) $display("xx cli: Bad ARP reply."); else $display("-> cli: ARP reply. %d.%d.%d.%d is at %h:%h:%h:%h:%h:%h", 
			data[28], data[29], data[30], data[31],
			mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
	endtask : arp_parse

	function [0:MTU-1][0:7] pack;
		input [7:0] data [0:MTU-1];
		input int len;
		for (int i = 0; i < len; i++) pack[i] = data[i];
	endfunction : pack

	// Extracts IPv4-specific data from stripped Ethernet frame
	task ipv4_parse;
		ref [7:0] data [0:MTU-1];
		ref int len;
		logic [7:0] data_tmp [0:MTU-1];
		logic [0:MTU-1][0:7] data_packed;
		ipv4_hdr_t ipv4_hdr;
		data_packed = pack(data, IPV4_HDR_LEN);
		ipv4_hdr[IPV4_HDR_LEN*8-1:0] = data_packed[0:19];
		$display("-> cli: IPv4 from %d.%d.%d.%d.", ipv4_hdr.src_ip[3], ipv4_hdr.src_ip[2], ipv4_hdr.src_ip[1], ipv4_hdr.src_ip[0]);
		for (int i = 0; i < len; i++) data_tmp[i] = data[i+IPV4_HDR_LEN];
		len = len - IPV4_HDR_LEN;
		data = data_tmp;
	endtask : ipv4_parse
	
	// Extracts ICMP-specific data from IPv4 packet
	task icmp_parse;
		ref [7:0] data [0:MTU-1];
		ref int len;
		output bit bad_frame;
		logic [7:0] data_tmp [0:MTU-1];
		ipv4_hdr_t ipv4_hdr;
		mac_addr_t src_mac;
		mac_addr_t dst_mac;
		for (int i = 0; i < len; i++) data_tmp[i] = data[i+ICMP_HDR_LEN];
		len = len - ICMP_HDR_LEN; // Payload length
		data = data_tmp;
	endtask : icmp_parse

	// Parses MAC frame, checks preamble and CRC. bad_frame is set '1' if an error is detected
	// Reduces len by 26
	task eth_parse;
		ref [7:0] data [0:MTU-1];
		ref int len;
		output bit bad_frame;
		output mac_addr_t src_mac;
		output mac_addr_t dst_mac;
		
		logic [7:0] data_tmp [0:MTU-1];
		logic [7:0][7:0] cur_preamble;
		bad_frame = 1; // assume frame is bad
		cur_preamble[7:0] = {data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7]};
		if (cur_preamble == {8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hd5}) begin
			for (int i = 0; i < len; i++) data[i] = data[i+8]; // Remove preamble to calculate checksum
		end else disable eth_parse;
		if (gen_crc(data, len-12) == {data[len-9], data[len-10], data[len-11], data[len-12]}); else begin // 12 for preamble and crc
			$display("xx cli: bad CRC.");
			disable eth_parse;
		end
		bad_frame = 0; // frame ok, clear flag
		src_mac = {data[0], data[1], data[2], data[3], data[4], data[5]};
		dst_mac = {data[6], data[7], data[8], data[9], data[10], data[11]};
		for (int i = 0; i < len; i++) data_tmp[i] = data[i+14]; // todo: 14 is actual mac hdr len
		data = data_tmp;
		len = len - 26; // 26 for: preamble + dst mac + src mac + ethertype + crc
	endtask : eth_parse

	///////////////////
	// Receive tasks //
	///////////////////

	task automatic timeout;
		input int ticks;
		output bit to;
		int ctr;
		to = 0;
		for (ctr = 0; ctr < ticks; ctr++) begin
			@ (posedge clk) ctr = ctr + 1;
		end
		to = 1;
	endtask : timeout

	// Receives a single packet. Packet must not have interruprions in valid signal
	// Outputs data and corresponding length
	task automatic receive;
		ref [7:0] rec_data [0:MTU-1];
		output int len;
		logic active;
		logic done;
		int ctr;
		ctr = 0;
		active = 0;
		done = 0;
		while (!done) begin
			@ (posedge clk) begin
				if (phy_rx.v) begin
					rec_data[ctr] = phy_rx.d;
					active = 1;
					ctr = ctr + 1;
				end
			end
			if (active && !phy_rx.v) done = 1;
			len = ctr;
		end
	endtask : receive

	// Uses "receive" task to receive data, but also waits for timeout
	task automatic receive_to; 
		ref [7:0] rec_data [0:MTU-1];
		output to;
		output int len;
		input int timeout_ticks;
		logic [7:0] rec_data_tmp [0:MTU-1];
			fork
				timeout(timeout_ticks, to);
				receive(rec_data_tmp, len);
			join_any
			disable fork;
			rec_data = rec_data_tmp;
			if (to) $display("xx cli: Timeout detected.");
	endtask : receive_to
endclass // pkt_gen_c

pkt_gen_c pkt_gen;

logic [7:0] data     [0:MTU-1];
logic [7:0] data_rec [0:MTU-1];
static reg [31:0] crc;
int len, len_payload;
bit to, bad_frame;
int f, f_dump;
parameter dump_file = "dump.txt";
mac_addr_t srv_mac_addr;

dev_t remote_dev;

assign remote_dev.ipv4_addr = srv_ipv4_addr;
assign remote_dev.mac_addr  = '1;
assign remote_dev.udp_port  = srv_udp_port;


initial begin
#100
	pkt_gen.ping (PING_FILE, local_dev, remote_dev); // Should not receive a packet, no ARP entry in server
	pkt_gen.arp_request(srv_ipv4_addr, srv_mac_addr, local_dev, to, bad_frame); // 
#1000
	pkt_gen.ping (PING_FILE, local_dev, remote_dev); // Should not receive a packet, no ARP entry in server
end

endmodule
