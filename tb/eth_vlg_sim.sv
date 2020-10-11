

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
      ARP_TABLE_SIZE  = 8,
      ARP_PACKET_SIZE = 28;
    
    parameter bit ARP_VERBOSE = 1;
    dev_t dev;
    localparam byte PREAMBLE [0:7] = {8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hd5};
    //function new(dev_t _dev);
    //  dev = _dev;
    //endfunction
    sim_arp_entry_t arp_table [0:2**ARP_TABLE_SIZE-1];
	mac_addr_t  MAC_ADDRESS;
    ipv4_t      IPV4_ADDRESS;
  function new (
	  mac_addr_t  _mac_addr,
      ipv4_t      _ipv4_addr
	);
    MAC_ADDRESS = _mac_addr;
    IPV4_ADDRESS = _ipv4_addr;
  endfunction : new
  
 //task automatic rx_engine;
 //  idle_s    : begin 
 //    
 //	end
 //  arp_req_s : begin 
 //    
 //	end
 //  arp_req_s : begin 
 //    
 //	end

 //endtask : rx_engine

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
      output byte pkt [0:MTU-1];
      int ctr = 0;
      int f;
      for (int i = 0; i < MTU; i++) pkt[i] = 8'hxx;
      begin
      //  $display("*** PKT GEN *** Reading file %s", file);
        $readmemh(file, pkt);
        while (pkt[ctr] !== 8'hxx) ctr = ctr + 1;
        len = ctr;
        for (int j = ctr; j < MTU; j++) pkt[j] = 0;
      //  $display("*** PKT GEN *** Done reading. Packet length: %d", len);
      end
    endtask : read_file

    function automatic fcs_t gen_fcs;
      input byte data [];
      bit [31:0] CRC_POLY = 32'hEDB88320;  
      bit [31:0] crc_table [255:0];
      bit [31:0] crc = '1;
    // Generate the table
      for (int i = 0; i < 256; i = i+1) begin
          crc_table[i] = i;
        for (int j = 0; j < 8; j = j+1) crc_table[i] = (crc_table[i][0] && 1'b1) ? (crc_table[i] >> 1) ^ CRC_POLY : crc_table[i] >> 1;
      end
      for (int i = 0; i < data.size(); i = i + 1) crc = crc_table[(crc[7:0]^data[i]) & 8'hff] ^ (crc >> 8); // Calculate The 
      gen_fcs = ~{crc[7:0], crc[15:8], crc[23:16], crc[31:24]};
    endfunction : gen_fcs

    // Checks FCS of an ethernet frame
    // Pass raw Ethernet frame with preamble and FCS
    task automatic check_fcs;
      input byte data [];
      output bit ok;
      fcs_t fcs, calc_fcs;
      byte data_fcs[];
      part_select(data, 8, data.size()-5, data_fcs);
     // $display("computing FCS over: %p", data_fcs);
      calc_fcs = gen_fcs(data_fcs);
      fcs = {>>{data with [data.size()-4+:4]}};
     // $display("eth FCS: %h., Calculated: %h", fcs, calc_fcs);
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
	bit ARP_VERBOSE = 1;
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
        if (ARP_VERBOSE) $display("Gateway ARP: Adding entry %d:%d:%d:%d - %h:%h:%h:%h:%h:%h",
		  ipv4[3], ipv4[2], ipv4[1], ipv4[0],
		  mac[5], mac[4], mac[3], mac[2], mac[1], mac[0]);
        arp_table[free_ptr].mac     = mac;
        arp_table[free_ptr].ipv4    = ipv4;
        arp_table[free_ptr].present = 1;
      end
      2'b01 : begin
        if (ARP_VERBOSE) $display("Gateway ARP: Updating MAC %h:%h:%h:%h:%h:%h for %d:%d:%d:%d",
		  ipv4[3], ipv4[2], ipv4[1], ipv4[0],
		  mac[5], mac[4], mac[3], mac[2], mac[1], mac[0]);
        arp_table[ipv4_ptr].mac     = mac;
        arp_table[ipv4_ptr].ipv4    = ipv4;
        arp_table[ipv4_ptr].present = 1;		
      end
      2'b10 : begin
        if (ARP_VERBOSE) $display("Gateway ARP: Updating IPv4 %d:%d:%d:%d for %h:%h:%h:%h:%h:%h",
		  ipv4[3], ipv4[2], ipv4[1], ipv4[0],
		  mac[5], mac[4], mac[3], mac[2], mac[1], mac[0]);
        arp_table[mac_ptr].mac     = mac;
        arp_table[mac_ptr].ipv4    = ipv4;
        arp_table[mac_ptr].present = 1;
      end
      2'b11 : begin
        if (mac_ptr == ipv4_ptr) begin
        //  if (ARP_VERBOSE) $display("Gateway ARP: No need to update");
        end
        else if (ipv4_ptr < mac_ptr) begin
          arp_table[mac_ptr].mac      = 0;
          arp_table[mac_ptr].ipv4     = 0;
          arp_table[mac_ptr].present  = 0;
          arp_table[ipv4_ptr].mac     = mac;
          arp_table[ipv4_ptr].ipv4    = ipv4;
          arp_table[ipv4_ptr].present = 1;
        end
        else if (ipv4_ptr > mac_ptr) begin
          arp_table[ipv4_ptr].mac     = 0;
          arp_table[ipv4_ptr].ipv4    = 0;
          arp_table[ipv4_ptr].present = 0;
          arp_table[mac_ptr].mac      = mac;
          arp_table[mac_ptr].ipv4     = ipv4;
          arp_table[mac_ptr].present  = 1;
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
  
   /* task automatic arp_request;
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
        arp_hdr_t arp_hdr;
    bit arp_ok;
      gen_arp_pkt(ipv4_addr, arp_hdr, data_tx, mac_hdr);
      gen_eth_pkt(data_tx, len_tx, mac_hdr); // Generate mac packet
     // receive(clk, d_in, v_in, data_rx, timed_out, ARP_TIMEOUT);
  
      if (timed_out) begin
        $display("xx cli: ARP request timeout.");
        disable arp_request;
      end

      else arp_parse(data_rx, arp_hdr, arp_ok);
      //$display("ipv4_addr: %d:%d:%d:%d", ipv4_addr[3], ipv4_addr[2], ipv4_addr[1], ipv4_addr[0]); 
      //$display("mac: %h:%h:%h:%h:%h:%h", mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
      to = 0;
    endtask : arp_request
  */
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
      //  $display("xx cli: ICMP packet too short.");
      //  disable ping;
      //end
      //data_tx_raw = data_tx; // Store raw ICMP data to compare with received
      //len_tx_raw = len_tx;
      //gen_icmp_pkt(data_tx, len_tx, dev, remote_dev.ipv4_addr, ipv4_hdr); // Send ping to
      //gen_ipv4_pkt(data_tx, len_tx, ipv4_hdr, remote_dev.mac_addr, remote_dev.mac_addr, mac_hdr);
      //gen_eth_pkt(data_tx, len_tx, mac_hdr);
      //send_pkt(clk, dout, vout, data_tx, len_tx);
      //
      //receive(clk, din, vin, data_rx, to, len_rx, 1000);
      //if (to) begin
      //  $display("xx cli: Ping timeout.");
      //  disable ping;
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
      input arp_hdr_t  hdr;
      output byte      data []; // generated packet is stored here
      mac_hdr_t mac_hdr; // header to generate mac frame
      // Task
      //$display("<- cli: ARP request from %d.%d.%d.%d at %h:%h:%h:%h:%h:%h to %d.%d.%d.%d",
      //  dev.ipv4_addr[3],
      //  dev.ipv4_addr[2],
      //  dev.ipv4_addr[1],
      //  dev.ipv4_addr[0],
      //  dev.mac_addr[5],
      //  dev.mac_addr[4],
      //  dev.mac_addr[3],
      //  dev.mac_addr[2],
      //  dev.mac_addr[1],
      //  dev.mac_addr[0],
      //  ipv4_addr[3],
      //  ipv4_addr[2],
      //  ipv4_addr[1],
      //  ipv4_addr[0]
      //);
	  byte data_arp [];
	  bit padding [0:19];
	  {<<{padding}} = {20{8'h00}};
      data_arp = new[48];
      {>>{data_arp with [0:arp_vlg_pkg::HDR_LEN-1]}} = {>>{hdr}};
	  data_arp = new [48] (data_arp);

      // Padding 
      data_arp[arp_vlg_pkg::HDR_LEN:47] = {<<{padding}};
      mac_hdr.ethertype = eth_vlg_pkg::ARP;
      mac_hdr.src_mac_addr = MAC_ADDRESS;
      mac_hdr.dst_mac_addr = 48'hffffffffffff;
	  $display("Generated ARP packet, %p", data_arp);
      gen_eth_pkt(data_arp, data, mac_hdr); // Generate mac packet
	  $display("Generated Eth packet, %p", data);
    endtask : gen_arp_pkt
    
	task automatic gen_arp_reply;
      input ipv4_t     rem_ipv4;
      input mac_addr_t rem_mac;
	  output byte data[];
	  arp_hdr_t hdr;
	  hdr.hw_type       = 1;
      hdr.proto         = 16'h0800;
      hdr.hlen          = 6;
      hdr.plen          = 4;
      hdr.oper          = 1;
      hdr.src_mac_addr  = MAC_ADDRESS;
      hdr.src_ipv4_addr = IPV4_ADDRESS;
      hdr.dst_mac_addr  = rem_mac;
      hdr.dst_ipv4_addr = rem_ipv4;
      gen_arp_pkt(hdr, data);
	endtask : gen_arp_reply

    // Generates ICMP packet of type 8 code 0 (ICMP request)
    task automatic gen_icmp_pkt;
    // ports
    input ipv4_t      ipv4_addr;
    input icmp_hdr_t  hdr;
    input byte        data [];
    output ipv4_hdr_t ipv4_hdr;
    $display("");

    // set IPv4 header
    ipv4_hdr.ver    = 4;
    ipv4_hdr.ihl    = 5;
    ipv4_hdr.qos    = 0;
    ipv4_hdr.length = data.size() + 20;
    ipv4_hdr.id     = $random();
    ipv4_hdr.zero   = 0;
    ipv4_hdr.df     = 1;
    ipv4_hdr.mf     = 0;
    ipv4_hdr.fo     = 0;
    ipv4_hdr.ttl    = 128;
    ipv4_hdr.proto  = 1; // ICMP
    ipv4_hdr.src_ip = dev.ipv4_addr;
    ipv4_hdr.dst_ip = ipv4_addr;
    for (int i = data.size() + 1; i > 0; i--) data[i+(icmp_vlg_pkg::HDR_LEN-1)] = data[i-1]; // make space for ICMP header
    data[0] = 8; // echo request
    data[1] = 0; // code 0
    data[2:3] = {8'h00, 8'h00};
    data[4:7] = {8'h00, 8'h00, 8'h00, 8'h00};
      //$display("<- cli: ICMP packet from %d.%d.%d.%d to %d.%d.%d.%d",
      //  dev.ipv4_addr[3],
      //  dev.ipv4_addr[2],
      //  dev.ipv4_addr[1],
      //  dev.ipv4_addr[0],
      //  ipv4_addr[3],
      //  ipv4_addr[2],
      //  ipv4_addr[1],
      //  ipv4_addr[0]
      //);
    endtask : gen_icmp_pkt
  
    task automatic gen_ipv4_pkt;
      ref byte data [];
      ref int  len;
      input ipv4_hdr_t ipv4_hdr;
      input mac_addr_t src_mac; // Destination MAC
      input mac_addr_t dst_mac; // Destination MAC
      output mac_hdr_t mac_hdr;
      begin
        //$display("<- cli: IPv4 packet from %d.%d.%d.%d to %d.%d.%d.%d",
        //  dev.ipv4_addr[3],
        //  dev.ipv4_addr[2],
        //  dev.ipv4_addr[1],
        //  dev.ipv4_addr[0],
        //  ipv4_hdr.dst_ip[3],
        //  ipv4_hdr.dst_ip[2],
        //  ipv4_hdr.dst_ip[1],
        //  ipv4_hdr.dst_ip[0]
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
    task automatic gen_eth_pkt;
      // Ports
      input byte data_in [];
      output byte data_out [$];
      input mac_hdr_t mac_hdr;
      // Task
	    int len = data_in.size();
      fcs_t fcs;
	    data_out = new[len+36];
	    $display("data in length is %d", data_in.size());
	    $display("data in %p", data_in);
      fcs = gen_fcs(data_in);
	    data_out = {
        PREAMBLE, 
        mac_hdr.src_mac_addr[5],
        mac_hdr.src_mac_addr[4],
        mac_hdr.src_mac_addr[3],
        mac_hdr.src_mac_addr[2],
        mac_hdr.src_mac_addr[1],
        mac_hdr.src_mac_addr[0],
        mac_hdr.dst_mac_addr[5],
        mac_hdr.dst_mac_addr[4],
        mac_hdr.dst_mac_addr[3],
        mac_hdr.dst_mac_addr[2],
        mac_hdr.dst_mac_addr[1],
        mac_hdr.dst_mac_addr[0],
        mac_hdr.ethertype[1],
        mac_hdr.ethertype[0], 
        data_in,
        fcs[3], 
        fcs[2], 
        fcs[1],
        fcs[0]};
	    $display("current packet: %p", data_out);
    endtask : gen_eth_pkt

    ////////////////////
    // Packet parsers //
    ////////////////////

    // Parses ARP packet for sender's IPv4 and MAC
    task automatic arp_parse;
      input  byte      data_in [];
      output arp_hdr_t arp_hdr;
      output bit       ok = 0;
     // if (data_in.size() != ARP_PACKET_SIZE) disable arp_parse;
      arp_hdr = {>>{data_in with [0:ARP_PACKET_SIZE-1]}};
      ok = 1;
    endtask : arp_parse
  
    // Extracts IPv4-specific data from stripped Ethernet frame
    task automatic ipv4_parse;
      input byte data_in [];
      input byte data [];
      output ipv4_hdr_t hdr;
      output bit ok = 0;
      int len = data_in.size();
      hdr = {>>{data_in with [0:19]}};
	  data = new[data_in.size()-20];
	  data = {>>{data_in with [20:data_in.size()]}};
      if (hdr.ihl != 5) begin
        $error("IPv4 parser error: IPv4 Options not supported");
        disable ipv4_parse;
	  end
      ok = 1;
    endtask : ipv4_parse

    task automatic icmp_parse;
      input byte data_in [];
      input byte data [];
      output icmp_hdr_t hdr;
      output bit ok = 0;
      int len = data_in.size();
      hdr = {>>{data_in with [0:icmp_vlg_pkg::HDR_LEN-1]}};
	  data = new[data_in.size()-icmp_vlg_pkg::HDR_LEN];
	  data = {>>{data_in with [icmp_vlg_pkg::HDR_LEN:data_in.size()]}};
      ok = 1;
    endtask : icmp_parse

    task automatic udp_parse;
      input byte data_in [];
      input byte data [];
      output udp_hdr_t hdr;
      output bit ok = 0;
      int len = data_in.size();
      hdr = {>>{data_in with [0:udp_vlg_pkg::HDR_LEN-1]}};
	  data = new[data_in.size()-udp_vlg_pkg::HDR_LEN];
	  data = {>>{data_in with [udp_vlg_pkg::HDR_LEN:data_in.size()]}};
      ok = 1;
	endtask : udp_parse

    task automatic tcp_parse;
      input byte data_in [];
      input byte data [];
      output tcp_hdr_t hdr;
      output tcp_opt_hdr_t opt_hdr;
      output bit ok = 0;
      int len = data_in.size();
      hdr = {>>{data_in with [0:tcp_vlg_pkg::HDR_LEN-1]}};
	  opt_hdr = {>>{data_in with [tcp_vlg_pkg::HDR_LEN+:(hdr.tcp_offset << 2)]}};
	  data = new[data_in.size()-(tcp_vlg_pkg::HDR_LEN+(hdr.tcp_offset << 2))];
	  data = {>>{data_in with [tcp_vlg_pkg::HDR_LEN+(hdr.tcp_offset << 2):data_in.size()]}};
      ok = 1;
	endtask : tcp_parse

    // Parses MAC frame, checks preamble and CRC. bad_frame is set '1' if an error is detected
    // Reduces len by 26
    task automatic eth_parse;
      input byte data_in [];
      output byte data [];
      output mac_hdr_t hdr;
      output bit fcs_ok = 0;
      int len = data_in.size();
      data = new[len-26]; // 26 bytes are for preamble, header and fcs
      check_fcs(data_in, fcs_ok);
	  $display("packet: %p", data_in);
      if (!fcs_ok) disable eth_parse;
      hdr= {>>{data_in with [8:21]}};
      data = {>>{data_in with [22:len-5]}}; // todo: 14 is actual mac hdr len
  endtask : eth_parse
    
  task parse;
    input byte data_in [];
    output byte data_out [];
	output icmp_hdr_t icmp_hdr;
    output bit icmp_ok;
	output udp_hdr_t udp_hdr;
    output bit udp_ok;
	output tcp_hdr_t tcp_hdr;
	output tcp_opt_hdr_t tcp_opt_hdr;
    output bit tcp_ok;
    output ipv4_hdr_t ipv4_hdr;
    output bit ipv4_ok;
    output arp_hdr_t arp_hdr;
    output bit arp_ok;
    output mac_hdr_t mac_hdr;
    output bit ok;
	byte data_eth [];
	bit fcs_ok;
    eth_parse(data_in, data_eth, mac_hdr, fcs_ok);
	$display("Parsing packet");
	if (fcs_ok) $display("FCS status: ok"); else $display("FCS status: bad");
	//if (mac_hdr.dst_mac_addr != MAC_ADDRESS || mac_hdr.dst_mac_addr != '1) disable parse;
	if (!fcs_ok) disable parse;
    case (mac_hdr.ethertype)
      IPv4 : begin
	    $display("IPv4 detected");
	    ipv4_parse(data_eth, data_out, ipv4_hdr, ipv4_ok);
        if (ipv4_hdr.dst_ip != IPV4_ADDRESS || ipv4_hdr.dst_ip != '1) disable parse;
	    case (ipv4_hdr.proto)
	      ICMP : begin
            $display("ICMP detected");
	  	    icmp_parse(data_eth, data_out, icmp_hdr, icmp_ok);
	      end
          UDP : begin
            $display("UDP detected");
	  	    udp_parse(data_eth, data_out, udp_hdr, udp_ok);
	  	  end
	  	  TCP : begin
            $display("TCP detected");
	  	    tcp_parse(data_eth, data_out, tcp_hdr, tcp_opt_hdr, tcp_ok);
	  	  end
	    endcase
	  end
	  ARP : begin
        $display("ARP detected");
	    arp_parse(data_eth, arp_hdr, arp_ok);
		if (arp_ok) arp_put(arp_hdr.src_ipv4_addr, arp_hdr.src_mac_addr);
	  end
	  default : begin
	    $error("Task parse: Unknown Ethertype");
	    disable parse;
	  end
    endcase
    ok = 1;
  endtask : parse

  function part_select;
    input byte in [];
    input int start;
    input int stop;
    output byte out [];
   // $display("start: %d, stop %d", start, stop);
    if (start > stop) $error("Function part_select: start higher then stop");
    out = new[stop - start];
    out = {>>{in with [start:stop]}};
  endfunction
  ///////////////////
  // Receive tasks //
  ///////////////////
  
  // Receives a single packet. Packet must not have interruprions in valid signal
  // Outputs data and corresponding length
  task automatic receive;
    ref bit  clk;
    ref byte d;
    ref bit  v;
    ref byte data [];
    output bit timed_out;
    input  int timeout;
    int  timeout_ctr;
    bit  active;
    bit  done;
    int  ctr;
    byte data_queue [$];
    ctr = 0;
    active = 0;
    done = 0;
    timed_out = 1;
    v = 1;
    begin
      while (!done) begin
        @ (posedge clk) begin
          if (!active) timeout_ctr = timeout_ctr + 1;
          if (timeout_ctr == timeout) disable receive;
          if (v) begin
            timed_out = 0;
            active = 1;
            ctr = ctr + 1;
          end
        end
        if (active && !v) done = 1;
        data = data_queue;
      end
    end
  endtask : receive
  
  endclass : device_c

endpackage : eth_vlg_sim