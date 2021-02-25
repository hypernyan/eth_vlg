package arp_vlg_pkg;

  parameter int ARP_HDR_LEN = 28;
  import eth_vlg_pkg::*;
  
  typedef logic [1:0][7:0] arp_hw_t;
  typedef logic [1:0][7:0] arp_oper_t;
  typedef logic      [7:0] hlen_t;
  typedef logic      [7:0] plen_t;
  
  typedef struct packed {
    arp_hw_t    hw_type;
    ethertype_t proto;
    hlen_t      hlen;
    plen_t      plen;
    arp_oper_t  oper;
    mac_addr_t  src_mac;
    ipv4_t      src_ipv4_addr;
    mac_addr_t  dst_mac;
    ipv4_t      dst_ipv4_addr;
  } arp_hdr_t;

endpackage : arp_vlg_pkg