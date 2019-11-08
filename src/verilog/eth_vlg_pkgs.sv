
package eth_vlg_pkg;

	typedef logic [5:0][7:0] mac_addr_t;
	typedef logic [1:0][7:0] port_t; 
	typedef logic [1:0][7:0] length_t; 
	typedef logic [3:0][7:0] ipv4_t;
	typedef logic [1:0][7:0] checksum_t;
	typedef logic [1:0][7:0] ethertype_t;

	typedef struct packed {
		mac_addr_t mac_addr;
		ipv4_t     ipv4_addr;
		port_t     udp_port;
	} dev_t;

	localparam ethertype_t
		IPV4 = 16'h0800,
		ARP  = 16'h0806,
		WoL  = 16'h0842,
		RARP = 16'h8035,
		IPX  = 16'h8137,
		IPV6 = 16'h86DD
	;

endpackage : eth_vlg_pkg

package udp_vlg_pkg;

import eth_vlg_pkg::*;

typedef struct packed {
	port_t     src_port;
	port_t     dst_port;
	length_t   length;
	checksum_t checksum;
} udp_hdr_t;

typedef enum logic [2:0] {
	udp_idle_s,
	udp_hdr_s,
	udp_payload_s
} udp_fsm_t;

endpackage : udp_vlg_pkg

package mac_vlg_pkg;

import eth_vlg_pkg::*;

typedef logic [3:0][7:0] fcs_t;
typedef logic [1:0][7:0] qtag_t;

typedef struct packed {
	mac_addr_t   dst_mac_addr;
	mac_addr_t   src_mac_addr;
	ethertype_t  ethertype;
	qtag_t       tag;
	length_t     length;
} mac_hdr_t;

typedef enum logic [7:0] {
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

parameter BUF_SIZE = 10;
parameter TIMEOUT  = 1000;

parameter [15:0] IPv4 = 16'h0800;

parameter [7:0] ICMP = 1;
parameter [7:0] UDP  = 17;
parameter [7:0] TCP  = 6;

typedef logic [1:0][7:0] id_t;
typedef logic [7:0]      proto_t;
typedef logic [7:0]      qos_t;
typedef logic [3:0]      ver_t;
typedef logic [3:0]      ihl_t;
typedef logic [7:0]      ttl_t;
typedef logic [12:0]     fo_t;

typedef struct packed {
	ver_t      ver;
	ihl_t      ihl;
	qos_t      qos;
	length_t   length;
	id_t       id;
	bit        zero;
	bit        df;
	bit        mf;
	fo_t       fo;
	ttl_t      ttl;
	proto_t    proto;
	checksum_t checksum;
	ipv4_t     src_ip;
	ipv4_t     dst_ip;
} ipv4_hdr_t;

typedef struct packed {
	length_t   pl_len;
	length_t   fin;
	bit        nf;
} ipv4_hdr_frag_t; // internal logic 

typedef enum logic {
	frag_w_idle_s,
	frag_w_write_s
} frag_fsm_w_t;

typedef enum logic {
	frag_r_idle_s,
	frag_r_read_s
} frag_fsm_r_t;

endpackage : ip_vlg_pkg

package icmp_vlg_pkg;

parameter [7:0]
echo_reply      = 0,
echo_request    = 8,
timestamp       = 13,
timestamp_reply = 14,
traceroute      = 30;

typedef logic [7:0]      icmp_type_t;
typedef logic [7:0]      icmp_code_t;
typedef logic [1:0][7:0] icmp_checksum_t;
typedef logic [1:0][7:0] icmp_id_t;
typedef logic [1:0][7:0] icmp_seq_t;

typedef struct packed {
	icmp_type_t     icmp_type;
	icmp_code_t     icmp_code;
	icmp_checksum_t icmp_checksum;
	icmp_id_t       icmp_id;
	icmp_seq_t      icmp_seq;
} icmp_hdr_t;

endpackage : icmp_vlg_pkg

package arp_vlg_pkg;

import eth_vlg_pkg::*;

typedef logic [1:0][7:0] arp_hw_t;
typedef logic [1:0][7:0] arp_oper_t;
typedef logic      [7:0] hlen_t;
typedef logic      [7:0] plen_t;

typedef enum logic {
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
	mac_addr_t  dev_mac_addr;
	ipv4_t      dev_ipv4_addr;
} arp_hdr_t;

endpackage : arp_vlg_pkg
