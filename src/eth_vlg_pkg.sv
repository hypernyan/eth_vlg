package eth_vlg_pkg;
  
  typedef logic [5:0][7:0] mac_addr_t;
  typedef logic [1:0][7:0] port_t; 
  typedef logic [1:0][7:0] length_t; 
  typedef logic [3:0][7:0] ipv4_t;
  typedef logic [1:0][7:0] cks_t;
  typedef logic [1:0][7:0] ethertype_t;

  typedef struct packed {
    mac_addr_t mac_addr;
    ipv4_t     ipv4_addr;
  } dev_t;
  
  typedef struct packed {
    logic [7:0] dat;
    logic       val;
    logic       sof;
    logic       eof;
    logic       err;
  } stream_t;

  localparam ethertype_t
  IPv4 = 16'h0800,
  ARP  = 16'h0806,
  WoL  = 16'h0842,
  RARP = 16'h8035,
  IPX  = 16'h8137,
  IPV6 = 16'h86DD;

endpackage : eth_vlg_pkg