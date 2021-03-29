
// Arp entry 
interface arp_data ();
  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*;

  ipv4_t      ipv4_addr;
  mac_addr_t  mac_addr;
  logic       val; // MAC-IP pair is valid
  modport in  (input  ipv4_addr, mac_addr, val);
  modport out (output ipv4_addr, mac_addr, val);
  modport sva (input  ipv4_addr, mac_addr, val);
endinterface : arp_data

interface arp_tbl ();
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
endinterface : arp_tbl