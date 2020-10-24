

package eth_vlg_sim;

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;
import dhcp_vlg_pkg::*;
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
      arp_gen(ipv4_addr, arp_hdr, data_tx, mac_hdr);
      gen_eth(data_tx, len_tx, mac_hdr); // Generate mac packet
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
      //icmp_gen(data_tx, len_tx, dev, remote_dev.ipv4_addr, ipv4_hdr); // Send ping to
      //ipv4_gen(data_tx, len_tx, ipv4_hdr, remote_dev.mac_addr, remote_dev.mac_addr, mac_hdr);
      //gen_eth(data_tx, len_tx, mac_hdr);
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
    
    task automatic arp_gen;
    // Ports
      input arp_hdr_t hdr;
      output byte     data []; // generated packet is stored here
      mac_hdr_t       mac_hdr; // header to generate mac frame
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
      {>>{data_arp with [0:arp_vlg_pkg::ARP_HDR_LEN-1]}} = {>>{hdr}};
	    data_arp = new [48] (data_arp);

      // Padding 
      data_arp[arp_vlg_pkg::ARP_HDR_LEN:47] = {<<{padding}};
      mac_hdr.ethertype = eth_vlg_pkg::ARP;
      mac_hdr.src_mac_addr = MAC_ADDRESS;
      mac_hdr.dst_mac_addr = 48'hffffffffffff;
	    $display("Generated ARP packet, %p", data_arp);
      gen_eth(data_arp, data, mac_hdr); // Generate mac packet
	    $display("Generated Eth packet, %p", data);
    endtask : arp_gen
    
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
      arp_gen(hdr, data);
	endtask : gen_arp_reply

    // Generates ICMP packet of type 8 code 0 (ICMP request)
    task automatic icmp_gen;
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
      for (int i = data.size() + 1; i > 0; i--) data[i+(icmp_vlg_pkg::ICMP_HDR_LEN-1)] = data[i-1]; // make space for ICMP header
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
    endtask : icmp_gen

    task automatic udp_gen;
      input byte data_in [];
      output byte data [];
      input udp_hdr_t hdr;

      {>>{data with [0:UDP_HDR_LEN-1]}} = hdr;
      $display("generating UDP with data %p", data_in);
      $display("generated UDP with data %p", data);
  //    data = new[UDP_HDR_LEN](data);
      $display("generating UDP with data %p", data_in);
      $display("generated UDP with data %p", data);
      data = {data, data_in};
     //  {>>{data with [0:UDP_HDR_LEN-1]}} = hdr;
     //  {>>{data with [UDP_HDR_LEN+:data_in.size()]}} = data_in;
      $display("generating UDP with data %p", data_in);
      $display("generated UDP with data %p", data);
    endtask : udp_gen

    task automatic ipv4_gen;
      input byte data_in [];
      output byte data [];
      input ipv4_hdr_t hdr;
      input mac_addr_t src_mac; // Destination MAC
      input mac_addr_t dst_mac; // Destination MAC
      output mac_hdr_t mac_hdr;
      begin
        {>>{data with [0:IPV4_HDR_LEN-1]}} = hdr;
    //    {>>{data with [IPV4_HDR_LEN+:data_in.size()]}} = data_in;
           data = {data, data_in};

        mac_hdr.ethertype = 16'h0800;
        mac_hdr.src_mac_addr = src_mac;
        mac_hdr.dst_mac_addr = dst_mac;
      end
    endtask : ipv4_gen
  
    // Reads 'data' and changes it according to mac header to be passed directly to phy
    task automatic gen_eth;
      // Ports
      input byte data_in [];
      output byte data_out [$];
      input mac_hdr_t mac_hdr;
      // Task
	    int len = data_in.size();
      fcs_t fcs;
      byte data_fcs[];
	    data_out = new[len+26];
	    data_fcs = new[len+14];
      data_fcs = {
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
        data_in
      };
      fcs = gen_fcs(data_fcs);
	    data_out = {
        PREAMBLE,
        data_fcs,
        fcs[3], 
        fcs[2], 
        fcs[1],
        fcs[0]
      };
    endtask : gen_eth

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
      output byte data [];
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
      output byte data [];
      output icmp_hdr_t hdr;
      output bit ok = 0;
      int len = data_in.size();
      hdr = {>>{data_in with [0:icmp_vlg_pkg::ICMP_HDR_LEN-1]}};
	    data = new[data_in.size()-icmp_vlg_pkg::ICMP_HDR_LEN];
	    data = {>>{data_in with [icmp_vlg_pkg::ICMP_HDR_LEN:data_in.size()]}};
      ok = 1;
    endtask : icmp_parse

    task automatic udp_parse;
      input byte data_in [];
      output byte data [];
      output udp_hdr_t hdr;
      output bit ok = 0;
      int len = data_in.size();
      hdr = {>>{data_in with [0:udp_vlg_pkg::UDP_HDR_LEN-1]}};
	    data = new[data_in.size()-udp_vlg_pkg::UDP_HDR_LEN];
	    data = {>>{data_in with [udp_vlg_pkg::UDP_HDR_LEN:data_in.size()]}};
      ok = 1;
	  endtask : udp_parse

    task automatic tcp_parse;
      input byte data_in [];
      output byte data [];
      output tcp_hdr_t hdr;
      output tcp_opt_hdr_t opt_hdr;
      output bit ok = 0;
      int len = data_in.size();
      hdr = {>>{data_in with [0:tcp_vlg_pkg::TCP_HDR_LEN-1]}};
	    opt_hdr = {>>{data_in with [tcp_vlg_pkg::TCP_HDR_LEN+:(hdr.tcp_offset << 2)]}};
	    data = new[data_in.size()-(tcp_vlg_pkg::TCP_HDR_LEN+(hdr.tcp_offset << 2))];
	    data = {>>{data_in with [tcp_vlg_pkg::TCP_HDR_LEN+(hdr.tcp_offset << 2):data_in.size()]}};
      ok = 1;
  	endtask : tcp_parse

    task automatic dhcp_parse;
      input  byte            data_in [];
      output dhcp_hdr_t      hdr;
      output dhcp_opt_hdr_t  opt_hdr;
      output dhcp_opt_pres_t opt_pres;
      output dhcp_opt_len_t  opt_len;
      output bit             ok = 0;

      byte opt_data [];
      dhcp_opt_field_t opt_field, nxt_opt_field;
      dhcp_opt_t cur_opt, nxt_opt;
      bit done;
      byte opt_cnt;
      byte cur_opt_len;
      int len = data_in.size();
      int opt_hdr_len = data_in.size() - dhcp_vlg_pkg::DHCP_HDR_LEN;
      logic [dhcp_vlg_pkg::OPT_LEN-1:0][7:0] cur_data;
      hdr = {>>{data_in with [0:dhcp_vlg_pkg::DHCP_HDR_LEN-1]}};
      opt_hdr  = 0;
      opt_pres = 0;
      opt_len  = 0;
      for (int i = dhcp_vlg_pkg::DHCP_HDR_LEN; i < len; i = i + 1) begin
        case (opt_field)
          dhcp_opt_field_kind : begin
            case (data_in[i])
              DHCP_OPT_MESSAGE_TYPE : begin
                $display("msg type");
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_message_type;
                opt_pres.dhcp_opt_message_type_pres = 1;
              end
              DHCP_OPT_SUBNET_MASK : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_subnet_mask;
                opt_pres.dhcp_opt_subnet_mask_pres = 1;
              end
              DHCP_OPT_RENEWAL_TIME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_renewal_time; 
                opt_pres.dhcp_opt_renewal_time_pres = 1; 
              end
              DHCP_OPT_REBINDING_TIME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_rebinding_time;
                opt_pres.dhcp_opt_rebinding_time_pres = 1;
              end
              DHCP_OPT_IP_ADDR_LEASE_TIME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_ip_addr_lease_time;  
                opt_pres.dhcp_opt_ip_addr_lease_time_pres = 1;  
              end
              DHCP_OPT_DHCP_CLIENT_ID : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_dhcp_client_id;
                opt_pres.dhcp_opt_dhcp_client_id_pres = 1;
              end
              DHCP_OPT_DHCP_SERVER_ID : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_dhcp_server_id;
                opt_pres.dhcp_opt_dhcp_server_id_pres = 1;
              end
              DHCP_OPT_ROUTER : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_router;
                opt_pres.dhcp_opt_router_pres = 1;
              end
              DHCP_OPT_DOMAIN_NAME_SERVER : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_domain_name_server;
                opt_pres.dhcp_opt_domain_name_server_pres = 1;
              end
              DHCP_OPT_DOMAIN_NAME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_domain_name;
                opt_pres.dhcp_opt_domain_name_pres = 1;
              end
              DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_fully_qualified_domain_name;
                opt_pres.dhcp_opt_fully_qualified_domain_name_pres = 1;               
              end
              DHCP_OPT_HOSTNAME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_hostname;
                opt_pres.dhcp_opt_hostname_pres = 1;                   
              end
              DHCP_OPT_PAD : begin
                nxt_opt_field = dhcp_opt_field_kind;
                cur_opt = dhcp_opt_pad;
              end
              DHCP_OPT_END : begin
                done = 1;
                nxt_opt_field = dhcp_opt_field_kind;
                cur_opt = dhcp_opt_end;
                opt_pres.dhcp_opt_end_pres = 1;
                $display("DHCP option end at %d", i);
              end
              default : begin
                nxt_opt_field = dhcp_opt_field_len;
              end
            endcase
            opt_cnt = 0;
            cur_data = 0;
            cur_opt_len = 0;
          end
          dhcp_opt_field_len : begin
            cur_opt_len = data_in[i];
            case (cur_opt)
              dhcp_opt_hostname                    : opt_len.dhcp_opt_hostname_len = cur_opt_len;
              dhcp_opt_domain_name                 : opt_len.dhcp_opt_domain_name_len = cur_opt_len;
              dhcp_opt_fully_qualified_domain_name : opt_len.dhcp_opt_fully_qualified_domain_name_len = cur_opt_len;
            endcase
            nxt_opt_field =  dhcp_opt_field_data;
            $display("DHCP option length: %d", cur_opt_len);
          end
          dhcp_opt_field_data : begin
            $display("msg type: %d", data_in[i]);
            cur_data[dhcp_vlg_pkg::OPT_LEN-1:0] = {cur_data[dhcp_vlg_pkg::OPT_LEN-2:0], data_in[i]};
            $display("cur data: %h. data in %h", cur_data, data_in[i]);
              $display("Current data to be written to opt: %h", cur_data);
              case (cur_opt)
                dhcp_opt_message_type                : opt_hdr.dhcp_opt_message_type                [dhcp_vlg_pkg::DHCP_OPT_MESSAGE_TYPE_LEN               -opt_cnt-1] = data_in[i]; 
                dhcp_opt_subnet_mask                 : opt_hdr.dhcp_opt_subnet_mask                 [dhcp_vlg_pkg::DHCP_OPT_SUBNET_MASK_LEN                -opt_cnt-1] = data_in[i];
                dhcp_opt_renewal_time                : opt_hdr.dhcp_opt_renewal_time                [dhcp_vlg_pkg::DHCP_OPT_RENEWAL_TIME_LEN               -opt_cnt-1] = data_in[i];
                dhcp_opt_rebinding_time              : opt_hdr.dhcp_opt_rebinding_time              [dhcp_vlg_pkg::DHCP_OPT_REBINDING_TIME_LEN             -opt_cnt-1] = data_in[i];
                dhcp_opt_ip_addr_lease_time          : opt_hdr.dhcp_opt_ip_addr_lease_time          [dhcp_vlg_pkg::DHCP_OPT_IP_ADDR_LEASE_TIME_LEN         -opt_cnt-1] = data_in[i];
                dhcp_opt_dhcp_server_id              : opt_hdr.dhcp_opt_dhcp_server_id              [dhcp_vlg_pkg::DHCP_OPT_DHCP_SERVER_ID_LEN             -opt_cnt-1] = data_in[i];
                dhcp_opt_dhcp_client_id              : opt_hdr.dhcp_opt_dhcp_client_id              [dhcp_vlg_pkg::DHCP_OPT_DHCP_CLIENT_ID_LEN             -opt_cnt-1] = data_in[i];
                dhcp_opt_router                      : opt_hdr.dhcp_opt_router                      [dhcp_vlg_pkg::DHCP_OPT_ROUTER_LEN                     -opt_cnt-1] = data_in[i];
                dhcp_opt_domain_name_server          : opt_hdr.dhcp_opt_domain_name_server          [dhcp_vlg_pkg::DHCP_OPT_DOMAIN_NAME_SERVER_LEN         -opt_cnt-1] = data_in[i];
                dhcp_opt_domain_name                 : opt_hdr.dhcp_opt_domain_name                 [dhcp_vlg_pkg::DHCP_OPT_DOMAIN_NAME_LEN                -opt_cnt-1] = data_in[i];
                dhcp_opt_fully_qualified_domain_name : opt_hdr.dhcp_opt_fully_qualified_domain_name [dhcp_vlg_pkg::DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME_LEN-opt_cnt-1] = data_in[i]; // Set which option fields are present
                dhcp_opt_hostname                    : opt_hdr.dhcp_opt_hostname                    [dhcp_vlg_pkg::DHCP_OPT_HOSTNAME_LEN                   -opt_cnt-1] = data_in[i];
              //dhcp_opt_end                         : opt_hdr.dhcp_opt_end                         = cur_data; // Set which option fields are present
              endcase
              opt_cnt = opt_cnt + 1;
              if (opt_cnt == cur_opt_len) nxt_opt_field = dhcp_opt_field_kind;
              $display("fucking data dhcp_opt_domain_name: %h", opt_hdr.dhcp_opt_domain_name);
              $display("fucking data dhcp_opt_domain_name nya: %h", cur_data);// << 8*(dhcp_vlg_pkg::OPT_LEN - cur_opt_len));
              //cur_data = cur_data << 8;
            end
        endcase
        opt_field = nxt_opt_field;
//cur_opt = nxt_opt;
      end
      ok = 1;
    endtask : dhcp_parse
    
    task automatic gen_dhcp_pkt;
      input dhcp_hdr_t      hdr;
      input dhcp_opt_hdr_t  opt_hdr;
      input dhcp_opt_pres_t opt_pres;
      input dhcp_opt_len_t  opt_len;
      output byte           data[$];
      udp_hdr_t      udp_hdr;
      ipv4_hdr_t     ipv4_hdr;
      mac_hdr_t mac_hdr;
      byte data_dhcp [];
      bit [dhcp_vlg_pkg::OPT_LEN-1:0][7:0] data_opt1;
      bit [dhcp_vlg_pkg::OPT_LEN-1:0][7:0] data_opt2;
      byte data_ipv4 [];
      byte data1 [];
      byte data2 [];
      byte data_udp [];
      int opt_num = 0;
      logic [dhcp_vlg_pkg::OPT_NUM-1:0][dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_hdr_proto; // 1 byte for end option
      logic [dhcp_vlg_pkg::OPT_LEN-1:0][7:0] data_opt;
      data_dhcp = new[dhcp_vlg_pkg::DHCP_HDR_LEN];
      data_dhcp = {>>{hdr}};
      $display("packet was: %p", data_dhcp);

      /*
      if (opt_pres.dhcp_opt_message_type_pres) begin
        $display("msg type was: %p", data_dhcp);
        data_dhcp = {data_dhcp, DHCP_OPT_MESSAGE_TYPE, DHCP_OPT_MESSAGE_TYPE_LEN, opt_hdr.dhcp_opt_message_type};
        $display("msg type now: %p", data_dhcp);
      end
      if (opt_pres.dhcp_opt_subnet_mask_pres) begin
        data_dhcp = {data_dhcp, DHCP_OPT_SUBNET_MASK, DHCP_OPT_SUBNET_MASK_LEN, opt_hdr.dhcp_opt_subnet_mask};
      end
      if (opt_pres.dhcp_opt_renewal_time_pres) begin
        data_dhcp = {data_dhcp, DHCP_OPT_RENEWAL_TIME, DHCP_OPT_RENEWAL_TIME_LEN, opt_hdr.dhcp_opt_renewal_time};
      end
      if (opt_pres.dhcp_opt_rebinding_time_pres) begin
        data_dhcp = {data_dhcp, DHCP_OPT_REBINDING_TIME, DHCP_OPT_REBINDING_TIME_LEN, opt_hdr.dhcp_opt_rebinding_time};
      end
      if (opt_pres.dhcp_opt_ip_addr_lease_time_pres) begin
        data_dhcp = {data_dhcp, DHCP_OPT_IP_ADDR_LEASE_TIME, DHCP_OPT_IP_ADDR_LEASE_TIME_LEN, opt_hdr.dhcp_opt_ip_addr_lease_time};
      end
      if (opt_pres.dhcp_opt_dhcp_server_id_pres) begin
        data_dhcp = {data_dhcp, DHCP_OPT_DHCP_SERVER_ID, DHCP_OPT_DHCP_SERVER_ID_LEN, opt_hdr.dhcp_opt_dhcp_server_id};
      end
      if (opt_pres.dhcp_opt_dhcp_client_id_pres) begin
        $display("cli id type was: %p", data_dhcp);
        data_dhcp = {data_dhcp, DHCP_OPT_DHCP_CLIENT_ID, DHCP_OPT_DHCP_CLIENT_ID_LEN, opt_hdr.dhcp_opt_dhcp_client_id};
        $display("cli id type now: %p", data_dhcp);
      end
      if (opt_pres.dhcp_opt_router_pres) begin
        data_dhcp = {data_dhcp, 
          DHCP_OPT_ROUTER,
          DHCP_OPT_ROUTER_LEN,
          opt_hdr.dhcp_opt_router
        };
      end
      if (opt_pres.dhcp_opt_domain_name_server_pres) begin
        $display("dns was : %p", data_dhcp);
        data_dhcp = {data_dhcp, 
          DHCP_OPT_DOMAIN_NAME_SERVER,
          DHCP_OPT_DOMAIN_NAME_SERVER_LEN,
          opt_hdr.dhcp_opt_domain_name_server[15:0]
         // opt_hdr.dhcp_opt_domain_name_server[2],
         // opt_hdr.dhcp_opt_domain_name_server[1],
         // opt_hdr.dhcp_opt_domain_name_server[0]
        };
        $display("dns now: %p", data_dhcp);
        $display("dns: %p", opt_hdr.dhcp_opt_domain_name_server);
      end
      if (opt_pres.dhcp_opt_domain_name_pres) begin
        $display("dn was: %p", data_dhcp);
        data_dhcp = {data_dhcp,
          DHCP_OPT_DOMAIN_NAME,
          opt_len.dhcp_opt_domain_name_len,
          opt_hdr.dhcp_opt_domain_name
        };
        $display("dn now: %p", data_dhcp);
        $display("dn: %p", {<<8{opt_hdr.dhcp_opt_domain_name}});
      end
      if (opt_pres.dhcp_opt_fully_qualified_domain_name_pres) begin
          data_dhcp = {data_dhcp,
          DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME, 
          opt_len.dhcp_opt_fully_qualified_domain_name_len,
          opt_hdr.dhcp_opt_fully_qualified_domain_name
        };
      end
      if (opt_pres.dhcp_opt_hostname_pres) begin
        data_dhcp = {data_dhcp,
        DHCP_OPT_HOSTNAME,
        opt_len.dhcp_opt_hostname_len, 
        opt_hdr.dhcp_opt_hostname
        };
      end
      if (opt_pres.dhcp_opt_end_pres) begin
        data_dhcp = {data_dhcp, DHCP_OPT_END};
      end
      */

      opt_hdr_proto = {
        {DHCP_OPT_MESSAGE_TYPE,                     DHCP_OPT_MESSAGE_TYPE_LEN,                        opt_hdr.dhcp_opt_message_type,                {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_MESSAGE_TYPE_LEN                        ){DHCP_OPT_PAD}}},
        {DHCP_OPT_SUBNET_MASK,                      DHCP_OPT_SUBNET_MASK_LEN,                         opt_hdr.dhcp_opt_subnet_mask,                 {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_SUBNET_MASK_LEN                         ){DHCP_OPT_PAD}}},
        {DHCP_OPT_RENEWAL_TIME,                     DHCP_OPT_RENEWAL_TIME_LEN,                        opt_hdr.dhcp_opt_renewal_time,                {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_RENEWAL_TIME_LEN                        ){DHCP_OPT_PAD}}}, 
        {DHCP_OPT_REBINDING_TIME,                   DHCP_OPT_REBINDING_TIME_LEN,                      opt_hdr.dhcp_opt_rebinding_time,              {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_REBINDING_TIME_LEN                      ){DHCP_OPT_PAD}}},                      
        {DHCP_OPT_IP_ADDR_LEASE_TIME,               DHCP_OPT_IP_ADDR_LEASE_TIME_LEN,                  opt_hdr.dhcp_opt_ip_addr_lease_time,          {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_IP_ADDR_LEASE_TIME_LEN                  ){DHCP_OPT_PAD}}},               
        {DHCP_OPT_DHCP_SERVER_ID,                   DHCP_OPT_DHCP_SERVER_ID_LEN,                      opt_hdr.dhcp_opt_dhcp_server_id,              {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_DHCP_SERVER_ID_LEN                      ){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DHCP_CLIENT_ID,                   DHCP_OPT_DHCP_CLIENT_ID_LEN,                      opt_hdr.dhcp_opt_dhcp_client_id,              {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_DHCP_CLIENT_ID_LEN                      ){DHCP_OPT_PAD}}},           
        {DHCP_OPT_HOSTNAME,                         opt_len.dhcp_opt_hostname_len,                    opt_hdr.dhcp_opt_hostname                     },  
        {DHCP_OPT_ROUTER,                           DHCP_OPT_ROUTER_LEN,                              opt_hdr.dhcp_opt_router,                      {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_ROUTER_LEN                              ){DHCP_OPT_PAD}}},    
        {DHCP_OPT_DOMAIN_NAME_SERVER,               DHCP_OPT_DOMAIN_NAME_SERVER_LEN,                  opt_hdr.dhcp_opt_domain_name_server,          {(dhcp_vlg_pkg::MAX_OPT_PAYLOAD-DHCP_OPT_DOMAIN_NAME_SERVER_LEN                  ){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DOMAIN_NAME,                      opt_len.dhcp_opt_domain_name_len,                 opt_hdr.dhcp_opt_domain_name                  },                  
        {DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME,      opt_len.dhcp_opt_fully_qualified_domain_name_len, opt_hdr.dhcp_opt_fully_qualified_domain_name  },   
        {{dhcp_vlg_pkg::OPT_LEN-1{DHCP_OPT_PAD}}, DHCP_OPT_END}
      };
      for (int i = 0; i < dhcp_vlg_pkg::OPT_NUM; i = i + 1) begin
        data_opt = opt_hdr_proto[dhcp_vlg_pkg::OPT_NUM-1-i];
        if (opt_pres[dhcp_vlg_pkg::OPT_NUM-1-i]) begin
          data_dhcp = new[data_dhcp.size()+dhcp_vlg_pkg::OPT_LEN](data_dhcp); //, {<<8{data_opt}}};
          data_dhcp[data_dhcp.size()-1-:dhcp_vlg_pkg::OPT_LEN] = {>>{data_opt}};
        end
        $display("data_opt: %p", data_opt);
        $display("data_dhcp: %p", data_dhcp);
      end
    // data_opt2 =  opt_hdr_proto[0];
    // data_opt1 =  opt_hdr_proto[1];
    //// data_opt1 =  {DHCP_OPT_DOMAIN_NAME,                      opt_len.dhcp_opt_domain_name_len,                 opt_hdr.dhcp_opt_domain_name};
    //
    // data1 = {>>{data_opt1}};
    // data2 = {>>{data_opt2}};
    // data_dhcp = {data_dhcp, data1};
    // $display("data1 is: %p", opt_hdr_proto);
    // $display("data2 is: %p", data2);
    // $display("packet is: %p", data_dhcp);
    // $display("data_opt1 is: %p", data_opt1);
    // $display("data_opt2 is: %p", data_opt2);
      // Set UDP header
      udp_hdr.src_port = DHCP_SRV_PORT;
      udp_hdr.dst_port = DHCP_CLI_PORT;
      udp_hdr.length   = data_dhcp.size() + UDP_HDR_LEN;
      udp_gen(data_dhcp, data_udp, udp_hdr);
      // Set IPv4 to broadcast
      ipv4_hdr.ver    = 4;
      ipv4_hdr.ihl    = 5;
      ipv4_hdr.qos    = 0;
      ipv4_hdr.length = udp_hdr.length + IPV4_HDR_LEN;
      ipv4_hdr.id     = 0; // todo something
      ipv4_hdr.zero   = 0; // 
      ipv4_hdr.df     = 0;
      ipv4_hdr.mf     = 0;
      ipv4_hdr.fo     = 0;
      ipv4_hdr.ttl    = 128;
      ipv4_hdr.proto  = UDP;
      ipv4_hdr.chsum  = 0;
      ipv4_hdr.src_ip = IPV4_ADDRESS;
      ipv4_hdr.dst_ip = {4{8'hff}};
      ipv4_gen(data_udp, data_ipv4, ipv4_hdr, MAC_ADDRESS, {6{8'hff}}, mac_hdr);
      gen_eth(data_ipv4, data, mac_hdr);
    endtask : gen_dhcp_pkt

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
    input  byte            data_in [];
    output byte            data_ipv4 [];
    output byte            data [];
    output icmp_hdr_t      icmp_hdr;
    output bit             icmp_ok;
    output udp_hdr_t       udp_hdr;
    output bit             udp_ok;
    output tcp_hdr_t       tcp_hdr;
    output tcp_opt_hdr_t   tcp_opt_hdr;
    output bit             tcp_ok;
    output ipv4_hdr_t      ipv4_hdr;
    output bit             ipv4_ok;
    output arp_hdr_t       arp_hdr;
    output bit             arp_ok;
    output mac_hdr_t       mac_hdr;
    output dhcp_hdr_t      dhcp_hdr;
    output dhcp_opt_hdr_t  dhcp_opt_hdr;
    output dhcp_opt_pres_t dhcp_opt_pres;
    output dhcp_opt_len_t  dhcp_opt_len;
    output bit             dhcp_ok;
    output bit             ok;

    byte data_eth [];
    bit fcs_ok;
    eth_parse(data_in, data_eth, mac_hdr, fcs_ok);
    $display("Parsing packet");
    if (fcs_ok) $display("FCS status: ok"); else $display("FCS status: bad");
  //if (mac_hdr.dst_mac_addr != MAC_ADDRESS || mac_hdr.dst_mac_addr != '1) disable parse;
    if (!fcs_ok) disable parse;
    case (mac_hdr.ethertype)
      IPv4 : begin
	      ipv4_parse(data_eth, data_ipv4, ipv4_hdr, ipv4_ok);
	      $display("IPv4 detected from %d:%d:%d:%d to %d:%d:%d:%d.",
            ipv4_hdr.src_ip[3],
            ipv4_hdr.src_ip[2],
            ipv4_hdr.src_ip[1],
            ipv4_hdr.src_ip[0],
            ipv4_hdr.dst_ip[3],
            ipv4_hdr.dst_ip[2],
            ipv4_hdr.dst_ip[1],
            ipv4_hdr.dst_ip[0]
          );
        //if (ipv4_hdr.dst_ip != IPV4_ADDRESS || ipv4_hdr.dst_ip != '1) disable parse;
	      case (ipv4_hdr.proto)
	        ICMP : begin
            $display("ICMP detected");
	  	      icmp_parse(data_ipv4, data, icmp_hdr, icmp_ok);
	        end
          UDP : begin
            $display("UDP detected");
	  	      udp_parse(data_ipv4, data, udp_hdr, udp_ok);
            if (udp_hdr.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT || udp_hdr.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT) begin
              dhcp_parse(data, dhcp_hdr, dhcp_opt_hdr, dhcp_opt_pres, dhcp_opt_len, dhcp_ok);
              $display("Detected DHCP with options %p", dhcp_opt_pres);
            end
	  	    end
	  	    TCP : begin
            $display("TCP detected");
	  	      tcp_parse(data_ipv4, data, tcp_hdr, tcp_opt_hdr, tcp_ok);
	  	    end
          default : begin
            $display("unknown IPv4 protocol");
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