package icmp_vlg_pkg;

  import ipv4_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*;

  parameter int ICMP_HDR_LEN = 8;
  parameter [7:0]
    echo_reply      = 0,
    echo_request    = 8,
    timestamp       = 13,
    timestamp_reply = 14,
    traceroute      = 30;
  
  typedef logic [7:0]      icmp_type_t;
  typedef logic [7:0]      icmp_code_t;
  typedef logic [1:0][7:0] icmp_cks_t;
  typedef logic [1:0][7:0] icmp_id_t;
  typedef logic [1:0][7:0] icmp_seq_t;

  typedef struct packed {
    icmp_type_t icmp_type;
    icmp_code_t icmp_code;
    icmp_cks_t  icmp_cks;
    icmp_id_t   icmp_id;
    icmp_seq_t  icmp_seq;
  } icmp_hdr_t;
  
  typedef struct packed {
    logic      val;
    length_t   length;
    icmp_hdr_t icmp_hdr;
    ipv4_hdr_t ipv4_hdr;
    mac_hdr_t  mac_hdr;
  } icmp_meta_t;

endpackage : icmp_vlg_pkg
