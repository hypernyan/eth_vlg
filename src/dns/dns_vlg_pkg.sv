package dns_vlg_pkg;

  import ipv4_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*;

  parameter int MAX_LEN = 16;
  parameter int QRY_LEN = 32;


  localparam [1:0][7:0] QUERRY_TYPE_A   = 1;
  localparam [1:0][7:0] QUERRY_CLASS_IN = 1;
  
  typedef logic [MAX_LEN-1:0][7:0] name_t;
  typedef logic [QRY_LEN-1:0][7:0] dns_qry_t;
  
  localparam port_t DNS_RND_PORT = 55555;
  localparam port_t DNS_PORT = 53;

  typedef struct packed {
    logic [1:0][7:0] dns_id;
    logic [1:0][7:0] dns_flags;
    logic [1:0][7:0] dns_queries;
    logic [1:0][7:0] dns_answers;
    logic [1:0][7:0] dns_auth_rr;
    logic [1:0][7:0] dns_add_rr;
  } dns_hdr_t;

  parameter int DNS_TOT_LEN = QRY_LEN + $bits(dns_hdr_t)/8;

  typedef struct packed {
    logic     val;
    logic [$clog2(DNS_TOT_LEN+1)-1:0] length;
    ipv4_t    dns_ipv4;
    dns_hdr_t hdr;
    dns_qry_t qry;
  } dns_meta_t;

endpackage : dns_vlg_pkg
