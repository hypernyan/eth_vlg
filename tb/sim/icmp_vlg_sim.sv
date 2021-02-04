package sim_icmp_pkg;
import sim_base_pkg::*;
import sim_ipv4_pkg::*;
import ipv4_vlg_pkg::*;
import icmp_vlg_pkg::*;
import eth_vlg_pkg::*;
import mac_vlg_pkg::*;

class device_icmp_c extends device_ipv4_c;
  task automatic icmp_gen;
    // ports
    input  ipv4_t     src_ipv4;
    input  ipv4_t     dst_ipv4;
    input  byte       data_in [];
    output byte       data    [];
    output ipv4_hdr_t ipv4_hdr;
    icmp_hdr_t hdr;
    byte       data_ipv4 [];
    mac_hdr_t mac_hdr;
    
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
    ipv4_hdr.src_ip = src_ipv4;
    ipv4_hdr.dst_ip = dst_ipv4;

    ipv4_gen(data_in, data_ipv4, ipv4_hdr, MAC_ADDRESS, {6{8'hff}}, mac_hdr);
    eth_gen(data_ipv4, data, mac_hdr);

    hdr.icmp_type  = 0; // echo request
    hdr.icmp_code  = 0; // code 0
    hdr.icmp_cks = 0;
    hdr.icmp_id    = 0;
    hdr.icmp_seq   = 0;
    {>>{data with [0:ICMP_HDR_LEN-1]}} = hdr;
    data = {data, data_in};
  endtask : icmp_gen

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
   //eth_gen(data_tx, len_tx, mac_hdr);
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

  endclass : device_icmp_c
endpackage : sim_icmp_pkg