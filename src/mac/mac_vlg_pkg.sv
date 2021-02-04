package mac_vlg_pkg;

  import eth_vlg_pkg::*;
  parameter [7:0][7:0] PREAMBLE = {8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hd5};
  typedef logic [3:0][7:0] fcs_t;
  typedef logic [1:0][7:0] qtag_t;
  localparam MAC_HDR_LEN = 22;

  typedef struct packed {
    mac_addr_t   dst_mac;
    mac_addr_t   src_mac;
    ethertype_t  ethertype;
  } mac_hdr_t;

  typedef struct packed {
    logic     val;
    mac_hdr_t hdr;
    length_t  length;
  } mac_meta_t;
  parameter mac_addr_t MAC_BROADCAST = {6{8'hff}};
  
endpackage : mac_vlg_pkg
