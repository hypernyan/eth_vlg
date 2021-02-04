package udp_vlg_pkg;

  import eth_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import ipv4_vlg_pkg::*;

  parameter UDP_HDR_LEN = 8;

  typedef struct packed {
    port_t   src_port;
    port_t   dst_port;
    length_t length;
    cks_t  cks;
  } udp_hdr_t;

  typedef struct packed {
    logic      val;
    logic      mac_known;
    udp_hdr_t  udp_hdr;
    ipv4_hdr_t ipv4_hdr;
    mac_hdr_t  mac_hdr;
  } udp_meta_t;

endpackage : udp_vlg_pkg