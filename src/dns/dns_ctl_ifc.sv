interface dns_ctl_ifc;
  import ipv4_vlg_pkg::*;
  import dns_vlg_pkg::*;
  import eth_vlg_pkg::*;

  ipv4_t ipv4_pri; // primary Domain Name Server IPv4 
  ipv4_t ipv4_sec; // seconary Domain Name Server IPv4 
  name_t name; // requested domain name 
  ipv4_t ipv4;   // DNS response of IPv4 
  logic  start;  // begin query
  logic  ready;  // query ready
  logic  error;  // error during query

  modport in  (input  ipv4_pri, ipv4_sec, name, start, output ipv4, ready, error);
  modport out (output ipv4_pri, ipv4_sec, name, start, input  ipv4, ready, error);

endinterface : dns_ctl_ifc