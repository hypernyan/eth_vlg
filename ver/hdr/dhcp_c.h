#ifndef DHCP_C_H
#define DHCP_C_H

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <list>
#include <iomanip>
#include <string>
#include "../hdr/udp_c.h"

class dhcp_c : virtual public udp_c {

  public :

    static constexpr int      DHCP_HDR_LEN              = 240;
    static constexpr uint16_t DHCP_CLI_PORT             = 68;
    static constexpr uint16_t DHCP_SRV_PORT             = 67;
    static constexpr uint8_t  OPT_LEN                   = 16;
    static constexpr uint8_t  MAX_OPT_PLD               = OPT_LEN - 2; // Option type and length take 2 bytes
    static constexpr uint32_t DHCP_COOKIE               = 0x63825363;
    // 
    static constexpr uint8_t DHCP_OPT_MSG_TYPE          = 53;
    static constexpr uint8_t DHCP_OPT_NET_MASK          = 1;
    static constexpr uint8_t DHCP_OPT_RENEW_TIME        = 58;
    static constexpr uint8_t DHCP_OPT_REBIND_TIME       = 59;
    static constexpr uint8_t DHCP_OPT_LEASE_TIME        = 51;
    static constexpr uint8_t DHCP_OPT_REQ_IP            = 50;
    static constexpr uint8_t DHCP_OPT_HOSTNAME          = 12;
    static constexpr uint8_t DHCP_OPT_DHCP_SRV_ID       = 54;
    static constexpr uint8_t DHCP_OPT_DHCP_CLI_ID       = 61;
    static constexpr uint8_t DHCP_OPT_ROUTER            = 3;
    static constexpr uint8_t DHCP_OPT_DNS               = 6;
    static constexpr uint8_t DHCP_OPT_DOMAIN_NAME       = 15;
    static constexpr uint8_t DHCP_OPT_FQDN              = 81;
    static constexpr uint8_t DHCP_OPT_END               = 255;
    static constexpr uint8_t DHCP_OPT_PAD               = 0;    
    //
    static constexpr uint8_t DHCP_OPT_MSG_TYPE_LEN      = 1;
    static constexpr uint8_t DHCP_OPT_NET_MASK_LEN      = 4;
    static constexpr uint8_t DHCP_OPT_RENEW_TIME_LEN    = 4;
    static constexpr uint8_t DHCP_OPT_REBIND_TIME_LEN   = 4;
    static constexpr uint8_t DHCP_OPT_LEASE_TIME_LEN    = 4;
    static constexpr uint8_t DHCP_OPT_REQ_IP_LEN        = 4;
    static constexpr uint8_t DHCP_OPT_DHCP_SRV_ID_LEN   = 4;
    static constexpr uint8_t DHCP_OPT_DHCP_CLI_ID_LEN   = 7;
    static constexpr uint8_t DHCP_OPT_ROUTER_LEN        = 4;
    static constexpr uint8_t DHCP_OPT_DNS_LEN           = 4;
    static constexpr uint8_t DHCP_OPT_DOMAIN_NAME_LEN   = MAX_OPT_PLD;
    static constexpr uint8_t DHCP_OPT_FQDN_LEN          = MAX_OPT_PLD;
    static constexpr uint8_t DHCP_OPT_HOSTNAME_LEN      = MAX_OPT_PLD;
    //
    static constexpr uint8_t DHCP_MSG_TYPE_BOOT_REQUEST = 1;
    static constexpr uint8_t DHCP_MSG_TYPE_BOOT_REPLY   = 2;
    //

    static constexpr size_t DHCP_OP_OFFSET      = 0;
    static constexpr size_t DHCP_HTYPE_OFFSET   = 1;
    static constexpr size_t DHCP_HLEN_OFFSET    = 2;
    static constexpr size_t DHCP_HOPS_OFFSET    = 3;
    static constexpr size_t DHCP_XID_OFFSET     = 4;
    static constexpr size_t DHCP_SECS_OFFSET    = 8;
    static constexpr size_t DHCP_FLAGS_OFFSET   = 10;
    static constexpr size_t DHCP_CLADDR_OFFSET  = 12;
    static constexpr size_t DHCP_YIADDR_OFFSET  = 16;
    static constexpr size_t DHCP_SIADDR_OFFSET  = 20;
    static constexpr size_t DHCP_GIADDR_OFFSET  = 24;
    static constexpr size_t DHCP_CHADDR_OFFSET  = 28;
    static constexpr size_t DHCP_SNAME_OFFSET   = 44;
    static constexpr size_t DHCP_FILE_OFFSET    = 108;
    static constexpr size_t DHCP_COOKIE_OFFSET  = 236;
    static constexpr size_t DHCP_OPTIONS_OFFSET = 240;

    typedef enum {
      DHCP_MSG_TYPE_DISCOVER     = 1,
      DHCP_MSG_TYPE_OFFER        = 2,
      DHCP_MSG_TYPE_REQUEST      = 3,
      DHCP_MSG_TYPE_DECLINE      = 4,
      DHCP_MSG_TYPE_ACK          = 5,
      DHCP_MSG_TYPE_NAK          = 6,
      DHCP_MSG_TYPE_RELEASE      = 7,
      DHCP_MSG_TYPE_INFORM       = 8
    } dhcp_msg_t;

    static const int MAC_OFFSET      = 22;
    static const int UDP_OFFSET      = 8;
    static const int FCS_BYTES       = 4;
    static const int PREAMBLE_BYTES  = 8;
    static const int MAC_ADDR_BYTES  = 6;

    struct msg_type_t {
      uint8_t val;
      bool pres;
    };

    struct net_mask_t {
      ipv4_t val;
      bool pres;
    };

    struct renew_time_t {
      uint32_t val;
      bool pres;
    };

    struct rebind_time_t {
      uint32_t val;
      bool pres;
    };

    struct lease_time_t {
      uint32_t val;
      bool pres;
    };

    struct req_ip_t {
      ipv4_t val;
      bool pres;
    };

    struct dhcp_srv_id_t {
      ipv4_t val;
      bool pres;
    };
    
    struct dhcp_cli_id_t {
      uint8_t len;
      uint8_t val [DHCP_OPT_DHCP_CLI_ID_LEN];
      bool pres;
    };

    struct hostname_t {
      uint8_t len;
      uint8_t val [MAX_OPT_PLD];
      bool pres;
    };

    struct router_t {
      ipv4_t val;
      bool pres;
    };

    struct dns_t {
      ipv4_t val;
      bool pres;
    };

    struct domain_name_t {
      uint8_t len;
      uint8_t val [MAX_OPT_PLD];
      bool pres;
    };
    
    struct fqdn_t {
      uint8_t len; 
      uint8_t flags; 
      uint8_t rcode1;
      uint8_t rcode2;
      uint8_t str [MAX_OPT_PLD-3];
      bool pres;
    };

    struct end_t {
      uint8_t val;
      bool pres;
    };

    struct chaddr_t {
      uint8_t val [16];
    };
    
    struct sname_t {
      uint8_t val [64];
    };
        
    struct bootfn_t {
      uint8_t val [128];
    };

    struct dhcp_hdr_t {
      uint8_t  op;
      uint8_t  htype;
      uint8_t  hlen;
      uint8_t  hops;
      uint32_t xid;
      uint16_t secs;
      uint16_t flags;
      ipv4_t   claddr;
      ipv4_t   yiaddr;
      ipv4_t   siaddr;
      ipv4_t   giaddr;
      chaddr_t chaddr;
      sname_t  sname;
      bootfn_t file;
      uint32_t cookie;
    };

    struct dhcp_opt_hdr_t {
      msg_type_t    msg_type;
      net_mask_t    net_mask;
      renew_time_t  renew_time;
      rebind_time_t rebind_time;
      lease_time_t  lease_time;
      req_ip_t      req_ip;
      dhcp_srv_id_t dhcp_srv_id;
      dhcp_cli_id_t dhcp_cli_id;
      hostname_t    hostname;
      router_t      router;
      dns_t         dns;
      domain_name_t domain_name;
      fqdn_t        fqdn;
      end_t         end;
    };

    struct dhcp_meta_t {
      dhcp_opt_hdr_t opt;
      dhcp_hdr_t hdr;
    };

    typedef enum {
      msg_type,
      net_mask,
      renew_time,
      rebind_time,
      lease_time,
      req_ip,
      dhcp_srv_id,
      dhcp_cli_id,
      hostname,
      router,
      dns,
      domain_name,
      fqdn,
      end,
      pad
    } dhcp_opt_t;
    
    typedef enum {
      kind,
      length,
      data
    } dhcp_field_t;

    dhcp_c (
      ipv4_t     _ipv4_addr,
      mac_addr_t _mac_addr,
      ipv4_t     _subnet_mask,
      ipv4_t     _router_addr,
      std::string _hostname,
      std::string _domain_name
    );
    
    ~dhcp_c();

    bool dhcp_process  (dhcp_meta_t& meta_rx, dhcp_meta_t& meta_tx);
    bool dhcp_parse    (std::vector<uint8_t>& pkt, dhcp_meta_t& meta);
    void dhcp_generate (dhcp_meta_t& meta, std::vector<uint8_t>& pkt);

  private:
    typedef enum {
      idle,
      offer_sent,
      wait_request,
      lease
    } dhcp_state_t;
    
    std::string dev_hostname;
    std::string dev_domain_name;

    ipv4_t ipv4_addr;
    ipv4_t subnet_mask;
    ipv4_t router_addr;
    mac_addr_t mac_addr;
    dhcp_state_t state;
};

#endif