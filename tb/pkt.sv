

package eth_vlg_sim;

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;
  typedef struct packed {
    ipv4_t ipv4;
    mac_addr_t mac;
    bit present;
  } sim_arp_entry_t;

  class device_c;
  
    localparam string PING_FILE = "ping.txt";
    localparam int
    MTU          = 9000,
    MAC_HDR_LEN  = 26,
    ICMP_HDR_LEN = 8,
    IPV4_HDR_LEN = 20,
    TCP_HDR_LEN  = 20,
    ARP_TIMEOUT  = 10000,
    ARP_TABLE_SIZE  = 8;
    
    parameter bit ARP_VERBOSE = 1;
    dev_t dev;
    localparam byte PREAMBLE [0:7] = {8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hd5};
    //function new(dev_t _dev);
    //  dev = _dev;
    //endfunction
    sim_arp_entry_t arp_table [0:2**ARP_TABLE_SIZE-1];
    task automatic engine;
      ref clk;
      ref byte din;
      ref bit  vin;
      ref byte dout;
      ref bit  vout;
      enum logic [2:0] {idle_s, receive_s, tramsmit_s} fsm;
  
      
      forever @ (posedge clk) begin
        case (fsm)
          idle_s : begin
            // if (vin) 
          end
        endcase
      end
    endtask
  	////////////////
  	// Common t&f //
  	////////////////
    
  	task automatic shift_data;
  		ref byte data [];
  		input int data_len;
  		input int shift_len;
  		for (int i = data_len+1; i > 0; i--) data[i+(shift_len-1)] = data[i-1];
  	endtask : shift_data
  
  	task automatic compare;
  		input [7:0] data_a [];
  		input [7:0] data_b [];
  		output bit equal;
  		equal = 0;
      if (data_a.size() != data_b.size()) disable compare;
  		for (int i = 0; i < data_a.size(); i++) if (data_a[i] != data_b[i]) disable compare;
  		equal = 1;
  	endtask : compare
  	
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
  
  	function automatic fcs_t gen_fcs;
  		input byte data [];
  		logic [31:0] CRC_POLY = 32'hEDB88320;	
  		logic [31:0] crc_table [255:0];
  		logic [31:0] crc = '1;
  		for (int i = 0; i < 256; i = i+1) begin
  	  		crc_table[i] = i;
  			for (int j = 0; j < 8; j = j+1) crc_table[i] = (crc_table[i][0] && 1'b1) ? (crc_table[i] >> 1) ^ CRC_POLY : crc_table[i] >> 1;
  		end
  		for (int i = 0; i < data.size(); i = i + 1) crc = crc_table[(crc[7:0]^data[i]) & 8'hff] ^ (crc >> 8);
  		gen_fcs = ~{crc[7:0], crc[15:8], crc[23:16], crc[31:24]};
  	endfunction : gen_fcs
  
    // Checks FCS of an ethernet frame
  	task automatic check_fcs;
  		input byte data [];
      output bit ok;
      fcs_t fcs, calc_fcs;
      byte data_fcs[];
      part_select(data, data_fcs, 8, data.size()-5);
      $display("computing FCS over: %p", data_fcs);
      calc_fcs = gen_fcs(data_fcs);
      fcs = {>>{data with [data.size()-4+:4]}};
      $display("eth FCS: %h., Calculated: %h", fcs, calc_fcs);
      ok = (fcs == calc_fcs);
  	endtask : check_fcs
  
  	function automatic [0:MTU-1][0:7] pack;
  		input byte data [];
  		for (int i = 0; i < data.size(); i++) pack[i] = data[i];
  	endfunction : pack
  
  	task automatic send_pkt;
      ref bit  clk;
      ref byte d;
      ref bit  v;
  		input byte data []; // generated packet is stored here
  		input int len;
  		for (int i = 0; i < len + MAC_HDR_LEN; i++) begin
  			@ (posedge clk) begin
  				d = data[i];
  				v = 1;
  			end
  		end
  		@ (posedge clk) begin
  			v = 0;
  			d = 0;
  		end
  	endtask : send_pkt
  
  	/////////////////////////
  	// Send and wait tasks //
  	/////////////////////////
    task automatic arp_put;
    input ipv4_t ipv4;
    input mac_addr_t mac;
    int free_ptr, mac_ptr, ipv4_ptr;
    bit ipv4_found, mac_found;
    for (int i = 0; i < 2**ARP_TABLE_SIZE; i = i + 1) begin
      if (!arp_table[i].present) free_ptr = i;
      if (arp_table[i].mac == mac && arp_table[i].present) begin
        mac_found = 1;
        mac_ptr = i;
      end
      if (arp_table[i].ipv4 == ipv4 && arp_table[i].present) begin
        ipv4_found = 1;
        ipv4_ptr = i;
      end
    end
    case ({mac_found, ipv4_found})
      2'b00 : begin
      //  if (ARP_VERBOSE) $display("Gateway ARP: Adding entry %d:%d:%d:%d : %h:%h:%h:%h:%h:%h");
        
      end
      2'b01 : begin
      //  if (ARP_VERBOSE) $display("Gateway ARP: Updating MAC %h:%h:%h:%h:%h:%h for %d:%d:%d:%d");
        
      end
      2'b10 : begin
      //  if (ARP_VERBOSE) $display("Gateway ARP: Updating IPv4 %d:%d:%d:%d for %h:%h:%h:%h:%h:%h");
        
      end
      2'b11 : begin
        if (mac_ptr == ipv4_ptr) begin
        //  if (ARP_VERBOSE) $display("Gateway ARP: No need to update");
        end
        else if (ipv4_ptr < mac_ptr) begin
          arp_table[mac_ptr].mac = 0;
          arp_table[mac_ptr].ipv4 = 0;
          arp_table[mac_ptr].present = 0;
          arp_table[ipv4_ptr].mac = mac;
          arp_table[ipv4_ptr].ipv4 = ipv4;
          arp_table[ipv4_ptr].present = 1;
        end
        else if (ipv4_ptr > mac_ptr) begin
          arp_table[ipv4_ptr].mac = 0;
          arp_table[ipv4_ptr].ipv4 = 0;
          arp_table[ipv4_ptr].present = 0;
          arp_table[mac_ptr].mac = mac;
          arp_table[mac_ptr].ipv4 = ipv4;
          arp_table[mac_ptr].present = 1;
        end
      end
    endcase
    endtask : arp_put
  
    task automatic arp_get;
      input ipv4_t ipv4;
      output mac_addr_t mac;
      output bit found;
      for (int i = 0; i < 2**ARP_TABLE_SIZE; i = i + 1) begin
        if (arp_table[i].ipv4 == ipv4 && arp_table[i].present) begin
          found = 1;
          mac = arp_table[i].mac;
        end
      end
    endtask : arp_get
  
  	task automatic arp_request;
      ref bit  clk;
      ref byte d_out;
      ref bit  v_out;
      ref logic [7:0] d_in;
      ref logic v_in;
  		input  ipv4_t     ipv4_addr;
  		output mac_addr_t mac_addr;
  		input  dev_t      dev;
  		output bit        to;
  		output bit        bad_frame;
  
  		byte data_tx [];
  		byte data_rx [];
      bit timed_out;
  		int len_tx, len_rx;
      mac_hdr_t mac_hdr;
  		gen_arp_pkt(ipv4_addr, dev, data_tx, len_tx, mac_hdr);
  		gen_pkt(data_tx, len_tx, mac_hdr); // Generate mac packet
  		send_pkt(clk, d_out, v_out, data_tx, len_tx);
  		receive(clk, d_in, v_in, data_rx, timed_out, ARP_TIMEOUT);
  
  		if (timed_out) begin
  			$display("xx cli: ARP request timeout.");
  			disable arp_request;
  		end
  		else arp_parse(data_rx, bad_frame, ipv4_addr, mac_addr);
  		//$display("ipv4_addr: %d:%d:%d:%d", ipv4_addr[3], ipv4_addr[2], ipv4_addr[1], ipv4_addr[0]); 
  		//$display("mac: %h:%h:%h:%h:%h:%h", mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
  		to = 0;
    endtask : arp_request
  
  	task automatic ping;
      ref bit clk;
  
      ref byte din;
      ref bit vin;
  
      ref byte dout;
      ref bit vout;
  
  		input string file;
  		input dev_t remote_dev;
  
  		byte data_tx [];
  		byte data_rx [];
  		byte data_tx_raw [];
  
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
  
  		//read_file(file, len_tx, data_tx); // Read file, copy to 'data'
  		//if (len_tx < 18) begin
  		//	$display("xx cli: ICMP packet too short.");
  		//	disable ping;
  		//end
  		//data_tx_raw = data_tx; // Store raw ICMP data to compare with received
  		//len_tx_raw = len_tx;
  		//gen_icmp_pkt(data_tx, len_tx, dev, remote_dev.ipv4_addr, ipv4_hdr); // Send ping to
  		//gen_ipv4_pkt(data_tx, len_tx, ipv4_hdr, remote_dev.mac_addr, remote_dev.mac_addr, mac_hdr);
  		//gen_pkt(data_tx, len_tx, mac_hdr);
  		//send_pkt(clk, dout, vout, data_tx, len_tx);
      //
  		//receive(clk, din, vin, data_rx, to, len_rx, 1000);
  		//if (to) begin
  		//	$display("xx cli: Ping timeout.");
  		//	disable ping;
  		//end
  		//eth_parse (data_rx, len_rx, bad_frame, src_mac, dst_mac);
  		//ipv4_parse (data_rx, len_rx);
  		//icmp_parse (data_rx, len_rx, bad_frame);
  		//compare(data_rx, data_tx_raw, len_rx, equal);
  		if (equal && (len_rx == len_tx_raw)) $display("-- cli: Ping OK."); else $display("xx cli: Ping error - bad reply. %d %d %d", len_rx, len_tx_raw, equal);
    endtask : ping
  
  	///////////////////////
  	// Packet generators //
  	///////////////////////
  
  	task automatic gen_arp_pkt;
		// Ports
		input ipv4_t ipv4_addr;
		input dev_t  dev;
		output byte data []; // generated packet is stored here
		output int len; // length of generated packet
		output mac_hdr_t mac_hdr; // header to generate mac frame
		// Task
		//$display("<- cli: ARP request from %d.%d.%d.%d at %h:%h:%h:%h:%h:%h to %d.%d.%d.%d",
		//	dev.ipv4_addr[3],
		//	dev.ipv4_addr[2],
		//	dev.ipv4_addr[1],
		//	dev.ipv4_addr[0],
		//	dev.mac_addr[5],
		//	dev.mac_addr[4],
		//	dev.mac_addr[3],
		//	dev.mac_addr[2],
		//	dev.mac_addr[1],
		//	dev.mac_addr[0],
		//	ipv4_addr[3],
		//	ipv4_addr[2],
		//	ipv4_addr[1],
		//	ipv4_addr[0]
		//);
		len = 46;
		data[0:27] = 
		{8'h0, 8'h1, 8'h08, 8'h00,
		 8'd6, 8'd4, 8'h0, 8'h1,
		 dev.mac_addr[5], dev.mac_addr[4], dev.mac_addr[3], dev.mac_addr[2], dev.mac_addr[1], dev.mac_addr[0],
		 dev.ipv4_addr[3], dev.ipv4_addr[2], dev.ipv4_addr[1], dev.ipv4_addr[0],
		 8'hff, 8'hff, 8'hff, 8'hff, 8'hff, 8'hff,
		 ipv4_addr[3], ipv4_addr[2], ipv4_addr[1], ipv4_addr[0]
		};
		// Padding 
		data[28:47] = {8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00};
		mac_hdr.ethertype = 16'h0806;
		mac_hdr.src_mac_addr = dev.mac_addr;
		mac_hdr.dst_mac_addr = 48'hffffffffffff;

  	endtask : gen_arp_pkt
  
  	// Generates ICMP packet of type 8 code 0 (ICMP request)
  	task automatic gen_icmp_pkt;
		// ports
		ref [7:0]         data [0:MTU-1];
		ref   int         len;
		input dev_t       dev;
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
		ipv4_hdr.src_ip   = dev.ipv4_addr;
		ipv4_hdr.dst_ip   = ipv4_addr;
		for (int i = len + 1; i > 0; i--) data[i+(ICMP_HDR_LEN-1)] = data[i-1]; // make space for ICMP header
		data[0] = 8; // echo request
		data[1] = 0; // code 0
		data[2:3] = {8'h00, 8'h00};
		data[4:7] = {8'h00, 8'h00, 8'h00, 8'h00};
		len = len + ICMP_HDR_LEN;
			//$display("<- cli: ICMP packet from %d.%d.%d.%d to %d.%d.%d.%d",
			//	dev.ipv4_addr[3],
			//	dev.ipv4_addr[2],
			//	dev.ipv4_addr[1],
			//	dev.ipv4_addr[0],
			//	ipv4_addr[3],
			//	ipv4_addr[2],
			//	ipv4_addr[1],
			//	ipv4_addr[0]
			//);
  	endtask : gen_icmp_pkt
  
  	task automatic gen_ipv4_pkt;
  		ref byte data [];
  		ref  int  len;
  		input ipv4_hdr_t ipv4_hdr;
  		input mac_addr_t src_mac; // Destination MAC
  		input mac_addr_t dst_mac; // Destination MAC
  		output mac_hdr_t mac_hdr;
  		begin
  			//$display("<- cli: IPv4 packet from %d.%d.%d.%d to %d.%d.%d.%d",
  			//	dev.ipv4_addr[3],
  			//	dev.ipv4_addr[2],
  			//	dev.ipv4_addr[1],
  			//	dev.ipv4_addr[0],
  			//	ipv4_hdr.dst_ip[3],
  			//	ipv4_hdr.dst_ip[2],
  			//	ipv4_hdr.dst_ip[1],
  			//	ipv4_hdr.dst_ip[0]
  			//);
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
  			mac_hdr.src_mac_addr = src_mac;
  			mac_hdr.dst_mac_addr = dst_mac;
  		end
  	endtask : gen_ipv4_pkt
  
  	// Reads 'data' and changes it according to mac header to be passed directly to phy
  	task automatic gen_pkt;
  		// Ports
  		ref byte data [];
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
  		crc = gen_fcs(data); // calculate crc
  		for (int i = 0; i < 4; i++) data[i+len+14] = crc[i]; // Append crc
  		for (int i = len+1+22; i > 0; i--) data[i+7] = data[i-1]; // Make space for preamble
  		data[0:7]  = {8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hd5};
  	endtask : gen_pkt
  
  	////////////////////
  	// Packet parsers //
  	////////////////////
  
  	// Parses ARP packet for sender's IPv4 and MAC
  	task automatic arp_parse;
  		ref byte data_in [];
  		output bit bad_frame;
  		output ipv4_t ipv4_addr; 
  		output mac_addr_t mac_addr;  
     // if (data.size() != )
     byte data [];
     mac_hdr_t mac_hdr;
  		eth_parse (data_in, data, bad_frame, mac_hdr);
  		ipv4_addr = {data[28], data[29], data[30], data[31]};
  		mac_addr  = {data[22], data[23], data[24], data[25], data[26], data[27]};
  		if (bad_frame) $display("xx cli: Bad ARP reply."); else $display("-> cli: ARP reply. %d.%d.%d.%d is at %h:%h:%h:%h:%h:%h", 
  			data[28], data[29], data[30], data[31],
  			mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
  	endtask : arp_parse
  
  	// Extracts IPv4-specific data from stripped Ethernet frame
  	task automatic ipv4_parse;
  		//ref byte data [];
  		//ref int len;
  		//logic [7:0] data_tmp [0:MTU-1];
  		//logic [0:MTU-1][0:7] data_packed;
  		//ipv4_hdr_t ipv4_hdr;
  		//data_packed = pack(data, IPV4_HDR_LEN);
  		//ipv4_hdr[IPV4_HDR_LEN*8-1:0] = data_packed[0:19];
  		//$display("-> cli: IPv4 from %d.%d.%d.%d.", ipv4_hdr.src_ip[3], ipv4_hdr.src_ip[2], ipv4_hdr.src_ip[1], ipv4_hdr.src_ip[0]);
  		//for (int i = 0; i < len; i++) data_tmp[i] = data[i+IPV4_HDR_LEN];
  		//len = len - IPV4_HDR_LEN;
  		//data = data_tmp;
  	endtask : ipv4_parse
  
  	// Extracts ICMP-specific data from IPv4 packet
  	task automatic icmp_parse;
  		//ref byte data [];
  		//ref int len;
  		//output bit bad_frame;
  		//byte data_tmp [0:MTU-1];
  		//ipv4_hdr_t ipv4_hdr;
  		//mac_addr_t src_mac;
  		//mac_addr_t dst_mac;
  		//for (int i = 0; i < len; i++) data_tmp[i] = data[i+ICMP_HDR_LEN];
  		//len = len - ICMP_HDR_LEN; // Payload length
  		//data = data_tmp;
  	endtask : icmp_parse
  
  	// Parses MAC frame, checks preamble and CRC. bad_frame is set '1' if an error is detected
  	// Reduces len by 26
  	task automatic eth_parse;
  		input byte data_in [];
  		output byte data [];
      output mac_hdr_t hdr;
  		output bit bad_frame = 1;

      bit fcs_ok;
  		int len = data_in.size();
      $display("entering eth_parse with packet %p of length %d", data_in, data_in.size());
      data = new[len-26]; // 26 bytes are for preamble, header and fcs
      $display("creating data array of length %d", len-26);

  		//if (data_in[0:7] != PREAMBLE) disable eth_parse;
      //part_select(data_in, data, 8, len-5);
      $display("part selected: %p", data);
      check_fcs(data_in, fcs_ok);
  		if (fcs_ok); else begin // 12 for preamble and crc
  			$display("xx cli: bad CRC.");
  		//	disable eth_parse;
  		end
  		bad_frame = 0; // frame ok, clear flag
  		hdr.src_mac_addr = {data_in[0], data_in[1], data_in[2], data_in[3], data_in[4], data_in[5]};
  		hdr.dst_mac_addr = {data_in[6], data_in[7], data_in[8], data_in[9], data_in[10], data_in[11]};
  		for (int i = 0; i < data_in.size(); i++) data[i] = data_in[i+14]; // todo: 14 is actual mac hdr len
  	endtask : eth_parse
    
    function part_select;
      input byte in [];
      output byte out [];
      input int start;
      input int stop;
      $display("start: %d, stop %d", start, stop);
      if (start > stop) $error("Function copy: start higher then stop");
      out = new[stop - start];
      {>>{out}} = {>>{in with [start:stop]}};
    endfunction
  	///////////////////
  	// Receive tasks //
  	///////////////////
  
  	// Receives a single packet. Packet must not have interruprions in valid signal
  	// Outputs data and corresponding length
  	task automatic receive;
      ref bit clk;
      ref logic [7:0] d;
      ref logic       v;
  		ref byte data [];
  		output bit timed_out;
  		input  int timeout;
      int   timeout_ctr;
  		logic active;
  		logic done;
  		int   ctr;
      byte data_queue [$];
  		ctr = 0;
  		active = 0;
  		done = 0;
      timed_out = 1;
  		while (!done) begin
  			@ (posedge clk) begin
          if (!active) timeout_ctr = timeout_ctr + 1;
          if (timeout_ctr == timeout) disable receive;
  				if (v) begin
            timed_out = 0;
  					data_queue.push_back(d);
  					active = 1;
  					ctr = ctr + 1;
  				end
  			end
  			if (active && !v) done = 1;
  		//	data = new[ctr];
        data = data_queue;
  		end
  	endtask : receive
  
  endclass : device_c

endpackage : eth_vlg_sim