package sim_tcp_pkg;
  import ipv4_vlg_pkg::*;
  import tcp_vlg_pkg::*;
  import sim_ipv4_pkg::*;

  class device_tcp_c extends ipv4_vlg_sim;

    task automatic tcp_parse;
      input byte data_in [];
      output byte data [];
      output tcp_hdr_t hdr;
      output tcp_opt_t opt;
      output bit ok = 0;
    // int len = data_in.size();
    // hdr = {>>{data_in with [0:tcp_vlg_pkg::TCP_HDR_LEN-1]}};
	  // opt_hdr = {>>{data_in with [tcp_vlg_pkg::TCP_HDR_LEN+:(hdr.tcp_offset << 2)]}};
	  // data = new[data_in.size()-(tcp_vlg_pkg::TCP_HDR_LEN+(hdr.tcp_offset << 2))];
	  // data = {>>{data_in with [tcp_vlg_pkg::TCP_HDR_LEN+(hdr.tcp_offset << 2):data_in.size()]}};
      ok = 1;
  	endtask : tcp_parse

  endclass : device_tcp_c

endpackage : sim_tcp_pkg