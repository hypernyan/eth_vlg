package ipv4_vlg_pkg;

  import eth_vlg_pkg::*;
  import mac_vlg_pkg::*;

  parameter int IPV4_HDR_LEN = 20;
  parameter int BUF_SIZE     = 10;
  parameter int TIMEOUT      = 1000;

  typedef logic [1:0][7:0] id_t;
  typedef logic [7:0]      proto_t;
  typedef logic [7:0]      qos_t;
  typedef logic [3:0]      ver_t;
  typedef logic [3:0]      ihl_t;
  typedef logic [7:0]      ttl_t;
  typedef logic [12:0]     fo_t;

  parameter proto_t ICMP = 1;
  parameter proto_t UDP  = 17;
  parameter proto_t TCP  = 6;

  parameter ipv4_t IPV4_BROADCAST = {4{8'hff}};

  typedef struct packed {
    ver_t    ver;
    ihl_t    ihl;
    qos_t    qos;
    length_t length;
    id_t     id;
    logic    zero;
    logic    df;
    logic    mf;
    fo_t     fo;
    ttl_t    ttl;
    proto_t  proto;
    cks_t    cks;
    ipv4_t   src_ip;
    ipv4_t   dst_ip;
  } ipv4_hdr_t;

  typedef struct packed {
    logic      mac_known;
    length_t   pld_len;
    ipv4_hdr_t ipv4_hdr;
    mac_hdr_t  mac_hdr;
  } ipv4_meta_t;

endpackage : ipv4_vlg_pkg
