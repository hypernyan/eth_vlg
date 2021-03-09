package sim_udp_pkg;
  import ipv4_vlg_pkg::*;
  import udp_vlg_pkg::*;
  import sim_ipv4_pkg::*;

  virtual class device_udp_c extends ipv4_vlg_sim;
  
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

    task automatic udp_gen;
      input  byte      data_in [];
      output byte      data    [];
      input  udp_hdr_t hdr;
      {>>{data with [0:UDP_HDR_LEN-1]}} = hdr;
      data = {data, data_in};
    endtask : udp_gen
  
  endclass : device_udp_c

endpackage : sim_udp_pkg