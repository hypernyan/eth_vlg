interface arp_data_ifc ();
  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*;

  ipv4_t      ipv4_addr;
  mac_addr_t  mac_addr;
  logic       val; // MAC-IP pair is valid
  modport in  (input  ipv4_addr, mac_addr, val);
  modport out (output ipv4_addr, mac_addr, val);
  modport sva (input  ipv4_addr, mac_addr, val);
endinterface : arp_data_ifc
