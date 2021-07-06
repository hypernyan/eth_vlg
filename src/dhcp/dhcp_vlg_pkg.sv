package dhcp_vlg_pkg;
  import eth_vlg_pkg::*;
  import ipv4_vlg_pkg::*;

  parameter int        DHCP_HDR_LEN  = 240;
  parameter port_t     DHCP_CLI_PORT = 68;
  parameter port_t     DHCP_SRV_PORT = 67;
  parameter [7:0]      OPT_LEN       = 16;
  parameter [7:0]      MAX_OPT_PLD = OPT_LEN - 2; // Option type and length take 2 bytes
  parameter [3:0][7:0] DHCP_COOKIE = {8'h63, 8'h82, 8'h53, 8'h63};

  parameter [7:0]
    // common
    DHCP_OPT_MSG_TYPE    = 8'd53,
    DHCP_OPT_NET_MASK    = 8'd1,
    DHCP_OPT_RENEW_TIME  = 8'd58,
    DHCP_OPT_REBIND_TIME = 8'd59,
    DHCP_OPT_LEASE_TIME  = 8'd51,
    DHCP_OPT_REQ_IP      = 8'd50,
    DHCP_OPT_HOSTNAME    = 8'd12,
    DHCP_OPT_DHCP_SRV_ID = 8'd54,
    DHCP_OPT_DHCP_CLI_ID = 8'd61,
    DHCP_OPT_ROUTER      = 8'd3,
    DHCP_OPT_DNS         = 8'd6,
    DHCP_OPT_DOMAIN_NAME = 8'd15,
    DHCP_OPT_FQDN        = 8'd81,
    DHCP_OPT_END         = 8'd255,
    DHCP_OPT_PAD         = 8'd0;

  parameter [7:0]
    DHCP_OPT_MSG_TYPE_LEN    = 8'd1,
    DHCP_OPT_NET_MASK_LEN    = 8'd4,
    DHCP_OPT_RENEW_TIME_LEN  = 8'd4,
    DHCP_OPT_REBIND_TIME_LEN = 8'd4,
    DHCP_OPT_LEASE_TIME_LEN  = 8'd4,
    DHCP_OPT_REQ_IP_LEN      = 8'd4,
    DHCP_OPT_DHCP_SRV_ID_LEN = 8'd4,
    DHCP_OPT_DHCP_CLI_ID_LEN = 8'd7,
    DHCP_OPT_ROUTER_LEN      = 8'd4,
    DHCP_OPT_DNS_LEN         = 8'd4,
    DHCP_OPT_DOMAIN_NAME_LEN = MAX_OPT_PLD,
    DHCP_OPT_FQDN_LEN        = MAX_OPT_PLD,
    DHCP_OPT_HOSTNAME_LEN    = MAX_OPT_PLD;

  parameter [7:0]
    DHCP_MSG_TYPE_BOOT_REQUEST = 8'd1,
    DHCP_MSG_TYPE_BOOT_REPLY   = 8'd2;

  parameter [7:0]
    DHCP_MSG_TYPE_DISCOVER = 8'd1,
    DHCP_MSG_TYPE_OFFER    = 8'd2,
    DHCP_MSG_TYPE_REQUEST  = 8'd3,
    DHCP_MSG_TYPE_DECLINE  = 8'd4,
    DHCP_MSG_TYPE_ACK      = 8'd5,
    DHCP_MSG_TYPE_NAK      = 8'd6,
    DHCP_MSG_TYPE_RELEASE  = 8'd7,
    DHCP_MSG_TYPE_INFORM   = 8'd8;

  typedef struct packed {
    logic dhcp_opt_msg_type_pres;
    logic dhcp_opt_net_mask_pres;
    logic dhcp_opt_renew_time_pres;
    logic dhcp_opt_rebind_time_pres;
    logic dhcp_opt_lease_time_pres;
    logic dhcp_opt_req_ip_pres;
    logic dhcp_opt_dhcp_srv_id_pres;
    logic dhcp_opt_dhcp_cli_id_pres;
    logic dhcp_opt_hostname_pres;
    logic dhcp_opt_router_pres;
    logic dhcp_opt_dns_pres;
    logic dhcp_opt_domain_name_pres;
    logic dhcp_opt_fqdn_pres;
    logic dhcp_opt_end_pres;
  } dhcp_opt_pres_t;

  parameter OPT_NUM    = $bits(dhcp_opt_pres_t);
  parameter OPT_NUM_TX = 7;

  parameter OPT_TOT_LEN    = OPT_NUM * OPT_LEN;
  parameter OPT_TOT_LEN_TX = OPT_NUM_TX * OPT_LEN;
  parameter HDR_TOT_LEN    = DHCP_HDR_LEN + OPT_TOT_LEN;
  parameter HDR_TOT_LEN_TX = DHCP_HDR_LEN + OPT_TOT_LEN_TX;

  typedef enum logic [0:13] {
    dhcp_opt_msg_type,
    dhcp_opt_net_mask,
    dhcp_opt_renew_time,
    dhcp_opt_rebind_time,
    dhcp_opt_lease_time,
    dhcp_opt_req_ip,
    dhcp_opt_dhcp_srv_id,
    dhcp_opt_dhcp_cli_id,
    dhcp_opt_hostname,
    dhcp_opt_router,
    dhcp_opt_dns,
    dhcp_opt_domain_name,
    dhcp_opt_fqdn,
    dhcp_opt_end,
    dhcp_opt_pad
  } dhcp_opt_t;

  typedef struct packed {
    logic [7:0] fqdn_flags; 
    logic [7:0] fqdn_rcode1;
    logic [7:0] fqdn_rcode2;
    logic [MAX_OPT_PLD-4:0][7:0] fqdn_str;   
  } dhcp_opt_fqdn_t;
  
  typedef struct packed {
    logic [7:0]                               dhcp_opt_msg_type;
    ipv4_t                                    dhcp_opt_net_mask;
    logic [3:0][7:0]                          dhcp_opt_renew_time;
    logic [3:0][7:0]                          dhcp_opt_rebind_time;
    logic [3:0][7:0]                          dhcp_opt_lease_time;
    ipv4_t                                    dhcp_opt_req_ip;
    ipv4_t                                    dhcp_opt_dhcp_srv_id;
    logic [DHCP_OPT_DHCP_CLI_ID_LEN-1:0][7:0] dhcp_opt_dhcp_cli_id;
    logic [MAX_OPT_PLD-1:0][7:0]              dhcp_opt_hostname;
    ipv4_t                                    dhcp_opt_router;
    ipv4_t                                    dhcp_opt_dns;
    logic [MAX_OPT_PLD-1:0][7:0]              dhcp_opt_domain_name;
    dhcp_opt_fqdn_t                           dhcp_opt_fqdn;
    logic [7:0]                               dhcp_opt_end;
  } dhcp_opt_hdr_t;

   typedef struct packed {
     logic [7:0] dhcp_opt_hostname_len; 
     logic [7:0] dhcp_opt_domain_name_len; 
     logic [7:0] dhcp_opt_fqdn_len; 
   } dhcp_opt_len_t; // variable length options

  typedef struct packed {
    logic          [7:0] dhcp_op;
    logic          [7:0] dhcp_htype;
    logic          [7:0] dhcp_hlen;
    logic          [7:0] dhcp_hops;
    logic  [3:0]   [7:0] dhcp_xid;
    logic  [1:0]   [7:0] dhcp_secs;
    logic  [1:0]   [7:0] dhcp_flags;
    ipv4_t               dhcp_cur_cli_addr;
    ipv4_t               dhcp_nxt_cli_addr;
    ipv4_t               dhcp_srv_ip_addr;
    ipv4_t               dhcp_retrans_addr;
    logic  [15:0]  [7:0] dhcp_chaddr;
    logic  [63:0]  [7:0] dhcp_sname;
    logic  [127:0] [7:0] dhcp_file;
    logic  [3:0]   [7:0] dhcp_cookie;
  } dhcp_hdr_t;

  typedef enum logic [2:0] {
    dhcp_opt_field_kind,
    dhcp_opt_field_len,
    dhcp_opt_field_data
  } dhcp_opt_field_t;

endpackage : dhcp_vlg_pkg
