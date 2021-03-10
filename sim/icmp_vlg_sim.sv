package sim_icmp_pkg;
  import base_vlg_sim::*;
  import sim_ipv4_pkg::*;
  import ipv4_vlg_pkg::*;
  import icmp_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import mac_vlg_pkg::*;
  
  class icmp_vlg_sim extends ipv4_vlg_sim;
  
    task automatic icmp_proc;
      input  byte data_in [];
      output byte data_out[];
      output bit  ok = 0;
      output bit  send = 0;
      byte data_icmp[];
      ipv4_hdr_t ipv4_hdr;
      icmp_hdr_t icmp_hdr;

      icmp_parse(data_in, data_icmp, ipv4_hdr, icmp_hdr, ok);
      if (!ok) disable icmp_proc;
      if (icmp_hdr.icmp_type == 0) begin
        icmp_gen(ipv4_hdr.src_ip, ipv4_hdr.dst_ip, data_icmp, data_out);
        send = 1;
      end
    endtask : icmp_proc

    protected task automatic icmp_parse;
      input  byte data_in  [];
      output byte data_out [];
      output ipv4_hdr_t ipv4_hdr;
      output icmp_hdr_t icmp_hdr;
      output bit ok = 0;

      bit fcs_ok, ipv4_ok;
      byte data_eth [];
      byte data_ipv4 [];
      mac_hdr_t mac_hdr;

      eth_parse(data_in, data_eth, mac_hdr, fcs_ok);
      if (!fcs_ok) disable icmp_parse;
      if (mac_hdr.ethertype != IPv4) disable icmp_parse;
      
      ipv4_parse(data_eth, data_ipv4, ipv4_hdr, ipv4_ok);
      if (!ipv4_ok) disable icmp_parse;
      if (ipv4_hdr.proto != ICMP) disable icmp_parse;

      icmp_hdr = {>>{data_ipv4 with [0:icmp_vlg_pkg::ICMP_HDR_LEN-1]}};
  	  data_out = new[data_ipv4.size()-icmp_vlg_pkg::ICMP_HDR_LEN];
  	  data_out = {>>{data_ipv4 with [icmp_vlg_pkg::ICMP_HDR_LEN:data_ipv4.size()]}};
      ok = 1;
    endtask : icmp_parse
 
    protected task automatic icmp_gen;
      input  ipv4_t src_ipv4;
      input  ipv4_t dst_ipv4;
      input  byte   data_in  []; // ICMP payload
      output byte   data_out []; 
      ipv4_hdr_t ipv4_hdr;
      icmp_hdr_t hdr;
      byte       data_ipv4 [];
      mac_hdr_t mac_hdr;
      
      ipv4_hdr.ver    = 4;
      ipv4_hdr.ihl    = 5;
      ipv4_hdr.qos    = 0;
      ipv4_hdr.length = data_in.size() + 20;
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
      eth_gen(data_ipv4, data_out, mac_hdr);
  
      hdr.icmp_type  = 0; // echo request
      hdr.icmp_code  = 0; // code 0
      hdr.icmp_cks = 0;
      hdr.icmp_id    = 0;
      hdr.icmp_seq   = 0;
      {>>{data_out with [0:ICMP_HDR_LEN-1]}} = hdr;
      data_out = {data_out, data_in};
    endtask : icmp_gen


  endclass : icmp_vlg_sim

endpackage : sim_icmp_pkg