interface arp_tbl_ifc; 
  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*; 
  ipv4_t     ipv4; // IPv4 address request
  logic      req;  // Request valid
  mac_addr_t mac;  // MAC assigned to ipv4
  logic      val;  // ARP request successful
  logic      err;  // ARP error
  modport in  (input  ipv4, req, output mac, val, err);
  modport out (output ipv4, req, input  mac, val, err);
  modport sva (input  ipv4, req,        mac, val, err);
endinterface : arp_tbl_ifc
