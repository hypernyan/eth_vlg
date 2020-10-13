
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

parameter HDR_LEN = 8;

typedef struct packed {
  port_t   src_port;
  port_t   dst_port;
  length_t length;
  chsum_t  chsum;
} udp_hdr_t;

endpackage : udp_vlg_pkg

package tcp_vlg_pkg;

import eth_vlg_pkg::*;

parameter int HDR_LEN = 20;
parameter int HDR_OPTIONS_POS = 13;

typedef bit [3:0][7:0] tcp_seq_num_t;
typedef bit [3:0][7:0] tcp_ack_num_t;
typedef bit      [3:0] tcp_offset_t;
typedef bit [1:0][7:0] tcp_win_size_t;
typedef bit [1:0][7:0] tcp_pointer_t;

typedef struct packed {
  bit        present; // present flag. "1" means data is valid
  chsum_t    chsum; // chsum for packet
  bit [31:0] start; // start address for the packet
  bit [31:0] stop; // expected ack for the packet
  bit [15:0] length; // start + length equals sequence number for current packet
  bit [31:0] timer; // Timer to retransmit unacked packet
  bit [7:0]  tries; // Times server has tried to retransmit
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

typedef enum bit [2:0] {
  tcp_opt_end,
  tcp_opt_nop,
  tcp_opt_mss,
  tcp_opt_win,
  tcp_opt_sack_perm,
  tcp_opt_sack,
  tcp_opt_timestamp
} tcp_opt_t;

typedef enum bit [2:0] {
  opt_field_kind,
  opt_field_len,
  opt_field_data
} tcp_opt_field_t;

localparam MAX_TCP_OPT_DATA_LEN = 8;
typedef bit [MAX_TCP_OPT_DATA_LEN-1:0][7:0] opt_data_t;

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

parameter int HDR_LEN = 8;
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

import eth_vlg_pkg::*;

parameter int HDR_LEN = 28;

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
