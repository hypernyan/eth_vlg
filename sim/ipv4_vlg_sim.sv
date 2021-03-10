package sim_ipv4_pkg;

  import base_vlg_sim::*;
  import ipv4_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import mac_vlg_sim::*;
  
  virtual class ipv4_vlg_sim extends mac_vlg_sim_c;
  
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
      if ((hdr.length != data_in.size()) && (data_in.size < 46)) $error("IPv4 parser error: Length mismatch. Expected %d. Got %d", data_in.size(), hdr.length);
      ok = 1;
    endtask : ipv4_parse
  
    task automatic ipv4_gen;
      input  byte data_in [];
      output byte data [];
      input  ipv4_hdr_t hdr;
      input  mac_addr_t src_mac; // Source MAC
      input  mac_addr_t dst_mac; // Destination MAC
      output mac_hdr_t  mac_hdr;
      begin
        {>>{data with [0:IPV4_HDR_LEN-1]}} = hdr;
        data = {data, data_in};
        mac_hdr.ethertype = 16'h0800;
        mac_hdr.src_mac = src_mac;
        mac_hdr.dst_mac = dst_mac;
      end
    endtask : ipv4_gen
  
  endclass : ipv4_vlg_sim

endpackage : sim_ipv4_pkg