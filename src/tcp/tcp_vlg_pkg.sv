package tcp_vlg_pkg;

  import ipv4_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*;

  parameter int TCP_DEFAULT_OFFSET      = 5;
  parameter int TCP_DEFAULT_WINDOW_SIZE = 5;
  parameter int TCP_HDR_LEN             = 20;
  parameter int HDR_OPTIONS_POS         = 12;
  parameter int MAX_TCP_OFFSET          = 15;
  parameter int TCP_MAX_WIN_SCALE       = 14;
  
  typedef logic [31:0]     tcp_num_t; // seq or ack
  typedef logic      [3:0] tcp_offset_t;
  typedef logic [1:0][7:0] tcp_wnd_t;    // window size type
  typedef logic      [7:0] tcp_scl_t;    // raw window scale type
  typedef logic [TCP_MAX_WIN_SCALE+$bits(tcp_wnd_t):0] tcp_wnd_scl_t; // scaled window type
  typedef logic [1:0][7:0] tcp_ptr_t;

  typedef logic [TCP_MAX_WIN_SCALE:0] tcp_scl_mult_t;

  // structure to keep info about each packet in tx buff
  typedef struct packed {
    logic        present; // present flag. "1" means data is valid
    logic        sacked;  // packet is SACKed. No need to retransmit it
    logic [31:0] cks;   // 32-logic checksum for packet with carry
    logic [31:0] start;   // beginning address for user data in buff RAM
    logic [31:0] stop;    // ending address for user data in buff RAM
    logic [15:0] length;  // start + length equals sequence number for current packet
    logic [31:0] timer;   // Timer to retransmit unacked packet
    logic [7:0]  tries;   // Times server has tried to retransmit
  } tcp_pkt_t;
  
  // transmission control block struct. store info on current connection
  typedef struct packed {
    port_t         loc_port;  // local  port
    port_t         rem_port;  // remote port
    ipv4_t         ipv4_addr; // remote ipv4
    mac_addr_t     mac_addr;  // remote MAC to skip arp table request
    logic          mac_known; // remote MAC is known
    tcp_num_t      loc_seq;   // current local  sequence number
    tcp_num_t      loc_ack;   // current local  acknowledgement number
    tcp_num_t      rem_seq;   // current remote sequence number
    tcp_num_t      rem_ack;   // current remote acknowledgement number
    tcp_scl_mult_t scl;       // window scale for multiplication (i.e. b10000 means x32 scaling)
    tcp_wnd_scl_t  wnd_scl;   // scaled window (meta.tcp_wnd_size*scl)
    logic          sack_perm; // sack permitted for current connection
  } tcb_t;
  
  typedef struct packed {
    logic ns;
    logic cwr;
    logic ece;
    logic urg;
    logic ack;
    logic psh;
    logic rst;
    logic syn;
    logic fin;
  } tcp_flags_t;

  parameter tcp_flags_t TCP_FLAG_NS  = 9'b100000000;
  parameter tcp_flags_t TCP_FLAG_CWR = 9'b010000000;
  parameter tcp_flags_t TCP_FLAG_ECE = 9'b001000000;
  parameter tcp_flags_t TCP_FLAG_URG = 9'b000100000;
  parameter tcp_flags_t TCP_FLAG_ACK = 9'b000010000;
  parameter tcp_flags_t TCP_FLAG_PSH = 9'b000001000;
  parameter tcp_flags_t TCP_FLAG_RST = 9'b000000100;
  parameter tcp_flags_t TCP_FLAG_SYN = 9'b000000010;
  parameter tcp_flags_t TCP_FLAG_FIN = 9'b000000001;

  typedef struct packed {
    port_t       src_port;
    port_t       dst_port;
    tcp_num_t    tcp_seq_num;
    tcp_num_t    tcp_ack_num;
    tcp_offset_t tcp_offset;
    logic [2:0]  reserved;
    tcp_flags_t  tcp_flags;
    tcp_wnd_t    tcp_wnd_size;
    cks_t        tcp_cks;
    tcp_ptr_t    tcp_pointer;
  } tcp_hdr_t;
  
  typedef struct packed {
    logic mss_pres;
    logic [1:0][7:0] mss;
  } tcp_opt_mss_t;
  
  typedef struct packed {
    logic wnd_pres;
    logic [7:0] wnd;
  } tcp_opt_wnd_t;
  
  typedef struct packed  {
    logic [31:0] left;
    logic [31:0] right;
  } sack_t;
  
  typedef struct packed  {
    logic [31:0] rec;
    logic [31:0] snd;
  } timestamp_t;
  
  typedef struct packed {
    logic        sack_pres;
    logic [2:0]  sack_blocks;
    logic [3:0]  block_pres;
    sack_t [3:0] sack;
  } tcp_opt_sack_t;
  
  typedef struct packed {
    logic sack_perm_pres;
  } tcp_opt_sack_perm_t;
  
  typedef struct packed {
    logic       timestamp_pres;
    timestamp_t timestamp;
  } tcp_opt_timestamp_t;
  
  typedef struct packed {
    tcp_opt_mss_t       tcp_opt_mss;       // 
    tcp_opt_wnd_t       tcp_opt_wnd;       // 
    tcp_opt_sack_t      tcp_opt_sack;      //
    tcp_opt_sack_perm_t tcp_opt_sack_perm; //
    tcp_opt_timestamp_t tcp_opt_timestamp; //
  } tcp_opt_hdr_t;
  
  typedef enum logic [6:0] {
    tcp_opt_end,
    tcp_opt_nop,
    tcp_opt_mss,
    tcp_opt_wnd,
    tcp_opt_sack_perm,
    tcp_opt_sack,
    tcp_opt_timestamp
  } tcp_opt_t;
  
  typedef enum logic [2:0] {
    tcp_opt_field_kind,
    tcp_opt_field_len,
    tcp_opt_field_data
  } tcp_opt_field_t;
  
  localparam OPT_LEN = 8;
  typedef logic [OPT_LEN-1:0][7:0] opt_data_t;
  
  localparam [7:0]
  TCP_OPT_END       = 0,
  TCP_OPT_NOP       = 1,
  TCP_OPT_MSS       = 2,
  TCP_OPT_WIN       = 3,
  TCP_OPT_SACK_PERM = 4,
  TCP_OPT_SACK      = 5,
  TCP_OPT_TIMESTAMP = 8;
  
  typedef struct packed {
    logic         val;
    tcp_hdr_t     tcp_hdr;
    tcp_opt_hdr_t tcp_opt_hdr;
    ipv4_hdr_t    ipv4_hdr;
    mac_hdr_t     mac_hdr;
    bit           mac_known;
    // Packet specific data
    length_t      pld_len;
    logic [31:0]  pld_cks;
  } tcp_meta_t;

  typedef struct packed {
    tcp_num_t     seq;
    length_t      lng;
    logic [31:0]  cks;
  } tcp_pld_info_t;

  typedef enum logic [4:0] {
    tcp_closed         = 5'b00001,
    tcp_listening      = 5'b00010,
    tcp_connecting     = 5'b00100,
    tcp_connected      = 5'b01000,
    tcp_disconnecting  = 5'b10000
  } tcp_stat_t;

endpackage : tcp_vlg_pkg
