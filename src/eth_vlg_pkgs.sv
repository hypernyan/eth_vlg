
package eth_vlg_pkg;
  
  typedef bit [5:0][7:0] mac_addr_t;
  typedef bit [1:0][7:0] port_t; 
  typedef bit [1:0][7:0] length_t; 
  typedef bit [3:0][7:0] ipv4_t;
  typedef bit [1:0][7:0] chsum_t;
  typedef bit [1:0][7:0] ethertype_t;

  typedef struct packed {
    mac_addr_t mac_addr;
    ipv4_t     ipv4_addr;
    port_t     udp_port;
  } dev_t;

  localparam ethertype_t
    IPv4 = 16'h0800,
    ARP  = 16'h0806,
    WoL  = 16'h0842,
    RARP = 16'h8035,
    IPX  = 16'h8137,
    IPV6 = 16'h86DD
  ;

endpackage : eth_vlg_pkg

package udp_vlg_pkg;

import eth_vlg_pkg::*;

parameter UDP_HDR_LEN = 8;

typedef struct packed {
  port_t   src_port;
  port_t   dst_port;
  length_t length;
  chsum_t  chsum;
} udp_hdr_t;

endpackage : udp_vlg_pkg

package tcp_vlg_pkg;

parameter int TCP_HDR_LEN = 20;

import eth_vlg_pkg::*;

parameter int HDR_OPTIONS_POS = 13;

typedef bit [3:0][7:0] tcp_seq_num_t;
typedef bit [3:0][7:0] tcp_ack_num_t;
typedef bit      [3:0] tcp_offset_t;
typedef bit [1:0][7:0] tcp_win_size_t;
typedef bit [1:0][7:0] tcp_pointer_t;

typedef struct packed {
  bit        present; // present flag. "1" means data is valid
  bit [31:0] chsum;   // 32-bit checksum for packet with carry
  bit [31:0] start;   // beginning address for user data in queue RAM
  bit [31:0] stop;    // ending address for user data in queue RAM
  bit [15:0] length;  // start + length equals sequence number for current packet
  bit [31:0] timer;   // Timer to retransmit unacked packet
  bit [7:0]  tries;   // Times server has tried to retransmit
} tcp_pkt_t; // length is

typedef struct packed {
  port_t        port;
  ipv4_t        ipv4_addr;
  tcp_seq_num_t isn; // local
  tcp_seq_num_t loc_seq_num; // local
  tcp_ack_num_t loc_ack_num;
  tcp_seq_num_t rem_seq_num; // remote
  tcp_ack_num_t rem_ack_num;
  bit           sack_perm;
} tcb_t;

typedef struct packed {
  bit ns;
  bit cwr;
  bit ece;
  bit urg;
  bit ack;
  bit psh;
  bit rst;
  bit syn;
  bit fin;
} tcp_flags_t;

typedef struct packed {
  port_t         src_port;
  port_t         dst_port;
  tcp_seq_num_t  tcp_seq_num;
  tcp_ack_num_t  tcp_ack_num;
  tcp_offset_t   tcp_offset;
  bit [2:0]      reserved;
  tcp_flags_t    tcp_flags;
  tcp_win_size_t tcp_win_size;
  chsum_t        tcp_chsum;
  tcp_pointer_t  tcp_pointer;
} tcp_hdr_t;

typedef struct packed {
  bit mss_pres;
  bit [1:0][7:0] mss;
} tcp_opt_mss_t;

typedef struct packed {
  bit win_pres;
  bit [7:0] win;
} tcp_opt_win_t;

typedef struct packed  {
  bit [31:0] left;
  bit [31:0] right;
} sack_t;

typedef struct packed  {
  bit [31:0] rec;
  bit [31:0] snd;
} timestamp_t;

typedef struct packed {
  bit sack_pres;
  bit [2:0] sack_blocks;
  bit [3:0] block_pres;
  sack_t [3:0] sack;
} tcp_opt_sack_t;

typedef struct packed {
  bit sack_perm_pres;
} tcp_opt_sack_perm_t;

typedef struct packed {
  bit timestamp_pres;
  timestamp_t timestamp;
} tcp_opt_timestamp_t;

typedef struct packed {
  tcp_opt_mss_t       tcp_opt_mss;       // 
  tcp_opt_win_t       tcp_opt_win;       // 
  tcp_opt_sack_t      tcp_opt_sack;      //
  tcp_opt_sack_perm_t tcp_opt_sack_perm; //
  tcp_opt_timestamp_t tcp_opt_timestamp; //
} tcp_opt_hdr_t;

typedef enum bit [6:0] {
  tcp_opt_end,
  tcp_opt_nop,
  tcp_opt_mss,
  tcp_opt_win,
  tcp_opt_sack_perm,
  tcp_opt_sack,
  tcp_opt_timestamp
} tcp_opt_t;

typedef enum bit [2:0] {
  tcp_opt_field_kind,
  tcp_opt_field_len,
  tcp_opt_field_data
} tcp_opt_field_t;

localparam OPT_LEN = 8;
typedef bit [OPT_LEN-1:0][7:0] opt_data_t;

localparam [7:0]
TCP_OPT_END       = 0,
TCP_OPT_NOP       = 1,
TCP_OPT_MSS       = 2,
TCP_OPT_WIN       = 3,
TCP_OPT_SACK_PERM = 4,
TCP_OPT_SACK      = 5,
TCP_OPT_TIMESTAMP = 8;

typedef enum bit [2:0] {
  tcp_idle_s,
  tcp_hdr_s,
  tcp_payload_s
} tcp_fsm_t;

typedef enum bit [8:0] {
  tcp_closed_s,
  tcp_listen_s,
  tcp_wait_syn_ack_s,
  tcp_syn_received_s,
  tcp_established_s,
  tcp_close_wait_s,
  tcp_send_fin_s,
  tcp_last_ack_s,
  tcp_send_ack_s
} tcp_srv_fsm_t;

endpackage : tcp_vlg_pkg

package mac_vlg_pkg;

import eth_vlg_pkg::*;

typedef bit [3:0][7:0] fcs_t;
typedef bit [1:0][7:0] qtag_t;

typedef struct packed {
  mac_addr_t   dst_mac_addr;
  mac_addr_t   src_mac_addr;
  ethertype_t  ethertype;
  qtag_t       tag;
  length_t     length;
} mac_hdr_t;

typedef enum bit [7:0] {
  idle_s,
  pre_s,
  dst_s,
  src_s,
  qtag_s,
  type_s,
  payload_s,
  fcs_s
} fsm_t;

endpackage : mac_vlg_pkg

package ip_vlg_pkg;

  import eth_vlg_pkg::*;

  parameter int IPV4_HDR_LEN  = 20;
  parameter int BUF_SIZE = 10;
  parameter int TIMEOUT  = 1000;

  typedef bit [1:0][7:0] id_t;
  typedef bit [7:0]      proto_t;
  typedef bit [7:0]      qos_t;
  typedef bit [3:0]      ver_t;
  typedef bit [3:0]      ihl_t;
  typedef bit [7:0]      ttl_t;
  typedef bit [12:0]     fo_t;

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
    bit      zero;
    bit      df;
    bit      mf;
    fo_t     fo;
    ttl_t    ttl;
    proto_t  proto;
    chsum_t  chsum;
    ipv4_t   src_ip;
    ipv4_t   dst_ip;
  } ipv4_hdr_t;

endpackage : ip_vlg_pkg

package icmp_vlg_pkg;

parameter int ICMP_HDR_LEN = 8;
parameter [7:0]
echo_reply      = 0,
echo_request    = 8,
timestamp       = 13,
timestamp_reply = 14,
traceroute      = 30;

typedef bit [7:0]      icmp_type_t;
typedef bit [7:0]      icmp_code_t;
typedef bit [1:0][7:0] icmp_chsum_t;
typedef bit [1:0][7:0] icmp_id_t;
typedef bit [1:0][7:0] icmp_seq_t;

typedef struct packed {
  icmp_type_t  icmp_type;
  icmp_code_t  icmp_code;
  icmp_chsum_t icmp_chsum;
  icmp_id_t    icmp_id;
  icmp_seq_t   icmp_seq;
} icmp_hdr_t;

endpackage : icmp_vlg_pkg

package arp_vlg_pkg;

parameter int ARP_HDR_LEN = 28;
import eth_vlg_pkg::*;


typedef bit [1:0][7:0] arp_hw_t;
typedef bit [1:0][7:0] arp_oper_t;
typedef bit      [7:0] hlen_t;
typedef bit      [7:0] plen_t;

typedef enum bit {
  arp_idle_s,
  arp_hdr_s
} arp_fsm_t;

typedef struct packed {
  arp_hw_t    hw_type;
  ethertype_t proto;
  hlen_t      hlen;
  plen_t      plen;
  arp_oper_t  oper;
  mac_addr_t  src_mac_addr;
  ipv4_t      src_ipv4_addr;
  mac_addr_t  dst_mac_addr;
  ipv4_t      dst_ipv4_addr;
} arp_hdr_t;

endpackage : arp_vlg_pkg

package dhcp_vlg_pkg;
  parameter int        DHCP_HDR_LEN       = 240;
  import eth_vlg_pkg::*;
  import ip_vlg_pkg::*;

  parameter port_t     DHCP_CLI_PORT = 68;
  parameter port_t     DHCP_SRV_PORT = 67;
  parameter byte       OPT_LEN       = 16;
  parameter byte       MAX_OPT_PAYLOAD = OPT_LEN - 2; // Option type and length take 2 bytes
  parameter [3:0][7:0] DHCP_COOKIE = {8'h63, 8'h82, 8'h53, 8'h63};

  parameter byte
    // common
    DHCP_OPT_MESSAGE_TYPE                    = 8'd53,
    DHCP_OPT_SUBNET_MASK                     = 8'd1,
    DHCP_OPT_RENEWAL_TIME                    = 8'd58,
    DHCP_OPT_REBINDING_TIME                  = 8'd59,
    DHCP_OPT_REQUESTED_IP_ADDRESS            = 8'd50,
    DHCP_OPT_HOSTNAME                        = 8'd12,
    DHCP_OPT_IP_ADDR_LEASE_TIME              = 8'd51,
    DHCP_OPT_DHCP_SERVER_ID                  = 8'd54,
    DHCP_OPT_DHCP_CLIENT_ID                  = 8'd61,
    DHCP_OPT_ROUTER                          = 8'd3,
    DHCP_OPT_DOMAIN_NAME_SERVER              = 8'd6,
    DHCP_OPT_DOMAIN_NAME                     = 8'd15,
    DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME     = 8'd81,
    DHCP_OPT_END                             = 8'd255,
    DHCP_OPT_PAD                             = 8'd0;

  parameter byte
    DHCP_OPT_MESSAGE_TYPE_LEN                = 8'd1,
    DHCP_OPT_SUBNET_MASK_LEN                 = 8'd4,
    DHCP_OPT_RENEWAL_TIME_LEN                = 8'd4,
    DHCP_OPT_REBINDING_TIME_LEN              = 8'd4,
    DHCP_OPT_IP_ADDR_LEASE_TIME_LEN          = 8'd4,
    DHCP_OPT_DHCP_SERVER_ID_LEN              = 8'd4,
    DHCP_OPT_DHCP_CLIENT_ID_LEN              = 8'd4,
    DHCP_OPT_ROUTER_LEN                      = 8'd4,
    DHCP_OPT_DOMAIN_NAME_SERVER_LEN          = 8'd4,
    DHCP_OPT_DOMAIN_NAME_LEN                 = MAX_OPT_PAYLOAD,
    DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME_LEN = MAX_OPT_PAYLOAD,
    DHCP_OPT_HOSTNAME_LEN                    = MAX_OPT_PAYLOAD;

  parameter byte
    DHCP_MSG_TYPE_DISCOVER = 8'd1,
    DHCP_MSG_TYPE_OFFER    = 8'd2,
    DHCP_MSG_TYPE_REQUEST  = 8'd3,
    DHCP_MSG_TYPE_DECLINE  = 8'd4,
    DHCP_MSG_TYPE_ACK      = 8'd5,
    DHCP_MSG_TYPE_NAK      = 8'd6,
    DHCP_MSG_TYPE_RELEASE  = 8'd7,
    DHCP_MSG_TYPE_INFORM   = 8'd8;

  typedef struct packed {
    bit dhcp_opt_message_type_pres;
    bit dhcp_opt_subnet_mask_pres;
    bit dhcp_opt_renewal_time_pres;
    bit dhcp_opt_rebinding_time_pres;
    bit dhcp_opt_ip_addr_lease_time_pres;
    bit dhcp_opt_dhcp_server_id_pres;
    bit dhcp_opt_dhcp_client_id_pres;
    bit dhcp_opt_hostname_pres;
    bit dhcp_opt_router_pres;
    bit dhcp_opt_domain_name_server_pres;
    bit dhcp_opt_domain_name_pres;
    bit dhcp_opt_fully_qualified_domain_name_pres;
    bit dhcp_opt_end_pres;
  } dhcp_opt_pres_t;

  parameter OPT_NUM = $bits(dhcp_opt_pres_t);
  parameter OPT_TOT_LEN = OPT_NUM * OPT_LEN;
  parameter HDR_TOT_LEN = DHCP_HDR_LEN + OPT_TOT_LEN;

  typedef enum bit [0:9] {
    dhcp_opt_message_type,
    dhcp_opt_subnet_mask,
    dhcp_opt_renewal_time,
    dhcp_opt_rebinding_time,
    dhcp_opt_ip_addr_lease_time,
    dhcp_opt_dhcp_server_id,
    dhcp_opt_dhcp_client_id,
    dhcp_opt_hostname,
    dhcp_opt_router,
    dhcp_opt_domain_name_server,
    dhcp_opt_domain_name,
    dhcp_opt_fully_qualified_domain_name,
    dhcp_opt_pad,
    dhcp_opt_end
  } dhcp_opt_t;

  typedef struct packed {
    logic [7:0]                              dhcp_opt_message_type;
    ipv4_t                                   dhcp_opt_subnet_mask;
    logic [3:0][7:0]                         dhcp_opt_renewal_time;
    logic [3:0][7:0]                         dhcp_opt_rebinding_time;
    logic [3:0][7:0]                         dhcp_opt_ip_addr_lease_time;
    ipv4_t                                   dhcp_opt_dhcp_server_id;
    ipv4_t                                   dhcp_opt_dhcp_client_id;
    logic [MAX_OPT_PAYLOAD-1:0] [7:0]        dhcp_opt_hostname;
    ipv4_t                                   dhcp_opt_router;
    ipv4_t                                   dhcp_opt_domain_name_server;
    logic [MAX_OPT_PAYLOAD-1:0] [7:0]        dhcp_opt_domain_name;
    logic [MAX_OPT_PAYLOAD-1:0] [7:0]        dhcp_opt_fully_qualified_domain_name; // Set which option fields are present
    logic [7:0]                              dhcp_opt_end; // Set which option fields are present
  } dhcp_opt_hdr_t;

   typedef struct packed {
     logic [7:0] dhcp_opt_hostname_len; 
     logic [7:0] dhcp_opt_domain_name_len; 
     logic [7:0] dhcp_opt_fully_qualified_domain_name_len; 
   } dhcp_opt_len_t; // variable length options

  typedef struct packed {
    logic [7:0]         dhcp_op;
    logic [7:0]         dhcp_htype;
    logic [7:0]         dhcp_hlen;
    logic [7:0]         dhcp_hops;
    logic [7:0] [3:0]   dhcp_xid;
    logic [7:0] [1:0]   dhcp_secs;
    logic [7:0] [1:0]   dhcp_flags;
    ipv4_t              dhcp_cur_cli_addr;
    ipv4_t              dhcp_nxt_cli_addr;
    ipv4_t              dhcp_srv_ip_addr;
    ipv4_t              dhcp_retrans_addr;
    logic [7:0] [15:0]  dhcp_chaddr;
    logic [7:0] [63:0]  dhcp_sname;
    logic [7:0] [127:0] dhcp_file;
    logic [7:0] [3:0]   dhcp_cookie;
  } dhcp_hdr_t;

  typedef enum bit [2:0] {
    dhcp_opt_field_kind,
    dhcp_opt_field_len,
    dhcp_opt_field_data
  } dhcp_opt_field_t;

endpackage : dhcp_vlg_pkg
