#include "../hdr/dhcp_c.h"

  dhcp_c::dhcp_c (
    ipv4_t     _ipv4_addr,
    mac_addr_t _mac_addr,
    ipv4_t     _subnet_mask,
    ipv4_t     _router_addr,
    std::string _hostname,
    std::string _domain_name
  ) {
    state = idle;
    ipv4_addr   = _ipv4_addr;
    mac_addr    = _mac_addr;
    subnet_mask = _subnet_mask;
    router_addr = _router_addr;
    dev_hostname    = _hostname;
    dev_domain_name = _domain_name;
  }

  dhcp_c::~dhcp_c() {

  }


  bool dhcp_c::dhcp_parse (std::vector<uint8_t>& pkt, dhcp_c::dhcp_meta_t& meta) {
    dhcp_c::dhcp_opt_t cur_opt;
    meta = {0};

    meta.hdr.op    = pkt[DHCP_OP_OFFSET   ];
    meta.hdr.htype = pkt[DHCP_HTYPE_OFFSET];
    meta.hdr.hlen  = pkt[DHCP_HLEN_OFFSET ];
    meta.hdr.hops  = pkt[DHCP_HOPS_OFFSET ];
    meta.hdr.xid   = extract_32(pkt, DHCP_XID_OFFSET  );
    meta.hdr.secs  = extract_16(pkt, DHCP_SECS_OFFSET );
    meta.hdr.flags = extract_16(pkt, DHCP_FLAGS_OFFSET);
  
    meta.hdr.claddr = extract_ip(pkt, DHCP_CLADDR_OFFSET);
    meta.hdr.yiaddr = extract_ip(pkt, DHCP_YIADDR_OFFSET);
    meta.hdr.siaddr = extract_ip(pkt, DHCP_SIADDR_OFFSET);
    meta.hdr.giaddr = extract_ip(pkt, DHCP_GIADDR_OFFSET);

    for (size_t i = 0; i < sizeof(chaddr_t); i++) meta.hdr.chaddr.val[i] = pkt[DHCP_CHADDR_OFFSET + i];
    for (size_t i = 0; i < sizeof(sname_t); i++)  meta.hdr.sname.val[i]  = pkt[DHCP_SNAME_OFFSET  + i];
    for (size_t i = 0; i < sizeof(bootfn_t); i++) meta.hdr.file.val[i]   = pkt[DHCP_FILE_OFFSET   + i];
    if (extract_32(pkt, DHCP_COOKIE_OFFSET) != DHCP_COOKIE) printf("[tb] Bad DHCP cookie\n");

    uint8_t opt_len;
    // options
    int opt_ctr = 0;
    dhcp_field_t field = kind;
    for (int i = DHCP_OPTIONS_OFFSET; i < (pkt.size() - FCS_BYTES); i++) {
      switch (field) {
        case (kind) :
          switch (pkt[i]) {
            case (DHCP_OPT_MSG_TYPE) :
              field = length;
              cur_opt = msg_type;
              meta.opt.msg_type.pres = 1;
            break;
            case (DHCP_OPT_NET_MASK) :
              field = length;
              cur_opt = net_mask;
              meta.opt.net_mask.pres = 1;
            break;
            case (DHCP_OPT_RENEW_TIME) :
              field = length;
              cur_opt = renew_time; 
              meta.opt.renew_time.pres = 1;
            break;
            case (DHCP_OPT_REBIND_TIME) :
              field = length;
              cur_opt = rebind_time;
              meta.opt.rebind_time.pres = 1;
            break;
            case (DHCP_OPT_LEASE_TIME) :
              field = length;
              cur_opt = lease_time;  
              meta.opt.lease_time.pres = 1;
            break;
            case (DHCP_OPT_REQ_IP) :
              field = length;
              cur_opt = req_ip;  
              meta.opt.req_ip.pres = 1;
              break;            
            case (DHCP_OPT_DHCP_CLI_ID) :
              field = length;
              cur_opt = dhcp_cli_id;
              meta.opt.dhcp_cli_id.pres = 1;
            break;
            case (DHCP_OPT_DHCP_SRV_ID) :
              field = length;
              cur_opt = dhcp_srv_id;
              meta.opt.dhcp_srv_id.pres = 1;
            break;
            case (DHCP_OPT_ROUTER) :
              field = length;
              cur_opt = router;
              meta.opt.router.pres = 1;
            break;
            case (DHCP_OPT_DNS) :
              field = length;
              cur_opt = dns;
              meta.opt.dns.pres = 1;
            break;
            case (DHCP_OPT_DOMAIN_NAME) :
              field = length;
              cur_opt = domain_name;
              meta.opt.domain_name.pres = 1;
            break;
            case (DHCP_OPT_FQDN) :
              field = length;
              cur_opt = fqdn;
              meta.opt.fqdn.pres = 1;
            break;
            case (DHCP_OPT_HOSTNAME) :
              field = length;
              cur_opt = hostname;
              meta.opt.hostname.pres = 1;
            break;
            case (DHCP_OPT_PAD) :
              field = kind;
              cur_opt = pad;
            break;
            case (DHCP_OPT_END) :
              field = kind;
              cur_opt = end;
            break;
            default :
              field = length;
            break;
          }
        break;
        case (length) :
          opt_len = pkt[i];
          switch (cur_opt) {
            case (hostname) :
              meta.opt.hostname.len = opt_len; 
            break;
            case (domain_name) :
              meta.opt.domain_name.len = opt_len; 
            break;
            case (fqdn) :
              meta.opt.fqdn.len = opt_len;
            break;
            default :
            break;
          }
          field = (opt_len == 0) ? kind : data;
          opt_ctr = 0;
        break;
        case (data) :
          opt_ctr = opt_ctr + 1;
          field = kind;
          switch (cur_opt) {
            case (msg_type) :
              meta.opt.msg_type.val = pkt[i];
            break;  
            case (net_mask) :
              meta.opt.net_mask.val = extract_ip(pkt, i);
              i = i + 3;
            break;
            case (renew_time) :
              meta.opt.renew_time.val = extract_32(pkt, i);
              i = i + 3;
            break;  
            case (rebind_time) :
              meta.opt.rebind_time.val = extract_32(pkt, i);
              i = i + 3;
            break;  
            case (lease_time) :
              meta.opt.lease_time.val = extract_32(pkt, i);
              i = i + 3;
            break;  
            case (req_ip) :
              meta.opt.req_ip.val = extract_ip(pkt, i);
              i = i + 3;
            break;
            case (dhcp_srv_id) :
              meta.opt.dhcp_srv_id.val = extract_ip(pkt, i);
              i = i + 3;
            break;  
            case (dhcp_cli_id) :
              for (uint8_t j = 0; j < opt_len - 2; j++) {
                meta.opt.dhcp_cli_id.val[j] = pkt[i];
                ++i;
              }
            break;
            case (hostname) :
              for (uint8_t j = 0; j < opt_len - 2; j++) {
                meta.opt.hostname.val[j] = pkt[i];
                ++i;
              }
            break;  
            case (router) :
              meta.opt.dhcp_srv_id.val = extract_ip(pkt, i);
              i = i + 3;
            break;
            case (dns) :
              meta.opt.dns.val = extract_ip(pkt, i);
              i = i + 3;
            break;  
            case (domain_name) :
              for (uint8_t j = 0; j < opt_len - 2; j++) {
                meta.opt.domain_name.val[j] = pkt[i];
              }
            break;
            case (fqdn) :
              for (uint8_t j = 0; j < sizeof(fqdn_t); j++) {
                switch (j) {
                  case (0) :
                    meta.opt.fqdn.flags  = pkt[i];
                  break;
                  case (1) :
                    meta.opt.fqdn.rcode1 = pkt[i];
                  break;
                  case (2) :
                    meta.opt.fqdn.rcode2 = pkt[i];
                  break;
                  default :
                    for (uint8_t j = 0; j < opt_len - 5; j++) {
                      meta.opt.fqdn.str[j] = pkt[i];
                    }
                  break;  
                }
                i++;
              }
            break;
            default :
            break;
          }
          field = kind;
        break;
      }
    }
    return true;
  }

  // returns true to send pkt_tx
  bool dhcp_c::dhcp_process (dhcp_meta_t& meta_rx, dhcp_meta_t& meta_tx) {
    printf("=== DHCP server (simulation) ===\n");
    if (!meta_rx.opt.msg_type.pres) {
      printf("Received DHCP packet without Message Type option\n");
      return false;
    }
    meta_tx = {0};
    switch (meta_rx.opt.msg_type.val) {
      case (DHCP_MSG_TYPE_DISCOVER) : {
        printf("DHCP Discover received\n");
        printf("Generating DHCP Offer\n");

        meta_tx.hdr.op               = DHCP_MSG_TYPE_BOOT_REPLY;
        meta_tx.hdr.htype            = 1;
        meta_tx.hdr.hlen             = 6;
        meta_tx.hdr.hops             = 0;
        meta_tx.hdr.xid              = meta_rx.hdr.xid;
        meta_tx.hdr.secs             = 0;
        meta_tx.hdr.flags            = 0x8000;
        meta_tx.hdr.claddr           = {0,   0,   0, 0};
        meta_tx.hdr.yiaddr           = meta_rx.opt.req_ip.val; //todo
        meta_tx.hdr.siaddr           = ipv4_addr; 
        meta_tx.hdr.giaddr           = {0,0,0,0}; 
        for (size_t i = 0; i < sizeof(mac_addr_t); i++) 
          meta_tx.hdr.chaddr.val[i] = mac_addr.m[i];
        meta_tx.hdr.sname            = {0};
        meta_tx.hdr.file             = {0};
        meta_tx.hdr.cookie           = DHCP_COOKIE;
       
        meta_tx.opt.msg_type.val     = DHCP_MSG_TYPE_OFFER;
        meta_tx.opt.net_mask.val     = subnet_mask;
        meta_tx.opt.renew_time.val   = 10;
        meta_tx.opt.rebind_time.val  = 15;
        meta_tx.opt.lease_time.val   = 20;
        meta_tx.opt.dhcp_srv_id.val  = ipv4_addr;
        meta_tx.opt.router.val       = ipv4_addr;
        meta_tx.opt.dns.val          = ipv4_addr;
        for (size_t i = 0; i < sizeof(dev_hostname); i++)  
          meta_tx.opt.hostname.val[i]    = dev_hostname[i];
        for (size_t i = 0; i < sizeof(dev_domain_name); i++)         
          meta_tx.opt.domain_name.val[i] = dev_domain_name[i];

        meta_tx.opt.hostname.len     = sizeof(dev_hostname);
        meta_tx.opt.domain_name.len  = sizeof(dev_domain_name); 
        meta_tx.opt.fqdn.len         = MAX_OPT_PLD;

        meta_tx.opt.msg_type.pres    = 1;
        meta_tx.opt.net_mask.pres    = 1;
        meta_tx.opt.renew_time.pres  = 1;
        meta_tx.opt.rebind_time.pres = 1;
        meta_tx.opt.lease_time.pres  = 1;
        meta_tx.opt.req_ip.pres      = 0;
        meta_tx.opt.dhcp_srv_id.pres = 0;
        meta_tx.opt.router.pres      = 0;
        meta_tx.opt.dns.pres         = 0;
        meta_tx.opt.hostname.pres    = 0;
        meta_tx.opt.domain_name.pres = 1;
        meta_tx.opt.fqdn.pres        = 0;
        meta_tx.opt.end.pres         = 1;
        break;
      }
      case (DHCP_MSG_TYPE_REQUEST) : {
        meta_tx.hdr.op               = DHCP_MSG_TYPE_BOOT_REPLY;
        meta_tx.hdr.htype            = 1;
        meta_tx.hdr.hlen             = 6;
        meta_tx.hdr.hops             = 0;
        meta_tx.hdr.xid              = meta_rx.hdr.xid;
        meta_tx.hdr.secs             = 0; 
        meta_tx.hdr.flags            = 0x8000;
        meta_tx.hdr.claddr           = {0,0,0,0}; 
        meta_tx.hdr.yiaddr           = meta_rx.opt.req_ip.val; //todo
        meta_tx.hdr.siaddr           = ipv4_addr; 
        meta_tx.hdr.giaddr           = {0}; 
        for (size_t i = 0; i < sizeof(mac_addr_t); i++) meta_tx.hdr.chaddr.val[i] = mac_addr.m[i];
        meta_tx.hdr.cookie           = DHCP_COOKIE;
        
        meta_tx.opt.msg_type.val     = DHCP_MSG_TYPE_ACK;
        meta_tx.opt.net_mask.val     = subnet_mask;
        meta_tx.opt.renew_time.val   = 10;
        meta_tx.opt.rebind_time.val  = 15;
        meta_tx.opt.lease_time.val   = 20;
        meta_tx.opt.dhcp_srv_id.val  = ipv4_addr;
        meta_tx.opt.router.val       = router_addr;
        meta_tx.opt.dns.val          = ipv4_addr;
        for (size_t i = 0; i < sizeof(dev_hostname); i++)              
          meta_tx.opt.hostname.val[i] = dev_hostname[i];
        for (size_t i = 0; i < sizeof(dev_domain_name); i++)           
          meta_tx.opt.domain_name.val[i] = dev_domain_name[i];
              
        meta_tx.opt.hostname.len     = sizeof(dev_hostname);
        meta_tx.opt.domain_name.len  = sizeof(dev_domain_name); 
        meta_tx.opt.fqdn.len         = MAX_OPT_PLD;

        meta_tx.opt.msg_type.pres    = 1;
        meta_tx.opt.net_mask.pres    = 1;
        meta_tx.opt.renew_time.pres  = 1;
        meta_tx.opt.rebind_time.pres = 1;
        meta_tx.opt.lease_time.pres  = 1;
        meta_tx.opt.dhcp_srv_id.pres = 1;
        meta_tx.opt.router.pres      = 1;
        meta_tx.opt.dns.pres         = 1;
        meta_tx.opt.hostname.pres    = 0;
        meta_tx.opt.domain_name.pres = 1;
        meta_tx.opt.fqdn.pres        = 0;
        meta_tx.opt.end.pres         = 1;
        break;
      }
      default : {
        printf("[SIM] DHCP Server: unknown message type");
        break;
      }
    }
  }

  void dhcp_c::dhcp_generate (dhcp_meta_t& meta, std::vector<uint8_t>& pkt) {
    // assemble dhcp header
      pkt.push_back(meta.hdr.op);
      pkt.push_back(meta.hdr.htype);
      pkt.push_back(meta.hdr.hlen);
      pkt.push_back(meta.hdr.hops);
      for (size_t i = 0; i < sizeof(uint32_t); i++) pkt.push_back((uint8_t)(meta.hdr.xid   >> (sizeof(uint32_t)-1-i)*8));
      for (size_t i = 0; i < sizeof(uint16_t); i++) pkt.push_back((uint8_t)(meta.hdr.secs  >> (sizeof(uint16_t)-1-i)*8));
      for (size_t i = 0; i < sizeof(uint16_t); i++) pkt.push_back((uint8_t)(meta.hdr.flags >> (sizeof(uint16_t)-1-i)*8));
      for (size_t i = 0; i < sizeof(ipv4_t);   i++) pkt.push_back(meta.hdr.claddr.i  [i]);
      for (size_t i = 0; i < sizeof(ipv4_t);   i++) pkt.push_back(meta.hdr.yiaddr.i  [i]);
      for (size_t i = 0; i < sizeof(ipv4_t);   i++) pkt.push_back(meta.hdr.siaddr.i  [i]);
      for (size_t i = 0; i < sizeof(ipv4_t);   i++) pkt.push_back(meta.hdr.giaddr.i  [i]);
      for (size_t i = 0; i < sizeof(chaddr_t); i++) pkt.push_back(meta.hdr.chaddr.val[i]);
      for (size_t i = 0; i < sizeof(sname_t);  i++) pkt.push_back(meta.hdr.sname.val [i]);
      for (size_t i = 0; i < sizeof(bootfn_t); i++) pkt.push_back(meta.hdr.file.val  [i]);
      for (size_t i = 0; i < sizeof(uint32_t); i++) pkt.push_back((uint8_t)(DHCP_COOKIE    >> (sizeof(uint32_t)-1-i)*8));
  
    // assemble dhcp options
    if (meta.opt.msg_type.pres) {
      pkt.push_back(DHCP_OPT_MSG_TYPE);
      pkt.push_back(DHCP_OPT_MSG_TYPE_LEN);
      pkt.push_back(meta.opt.msg_type.val);
    }
    if (meta.opt.net_mask.pres) {
      pkt.push_back(DHCP_OPT_NET_MASK);
      pkt.push_back(DHCP_OPT_NET_MASK_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.net_mask.val); i++) {
        pkt.push_back(meta.opt.net_mask.val.i[i]);
      }
    }
    if (meta.opt.renew_time.pres) {
      pkt.push_back(DHCP_OPT_RENEW_TIME);
      pkt.push_back(DHCP_OPT_RENEW_TIME_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.renew_time.val); i++) {
        pkt.push_back((uint8_t)(meta.opt.renew_time.val >> (sizeof(uint32_t)-1-i)*8));
      }
    }
    if (meta.opt.rebind_time.pres) {
      pkt.push_back(DHCP_OPT_REBIND_TIME);
      pkt.push_back(DHCP_OPT_REBIND_TIME_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.rebind_time.val); i++) {
        pkt.push_back((uint8_t)(meta.opt.rebind_time.val >> (sizeof(uint32_t)-1-i)*8));
      }
    }
    if (meta.opt.lease_time.pres) {
      pkt.push_back(DHCP_OPT_LEASE_TIME);
      pkt.push_back(DHCP_OPT_LEASE_TIME_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.lease_time.val); i++) {
        pkt.push_back((uint8_t)(meta.opt.lease_time.val >> (sizeof(uint32_t)-1-i)*8));
      }
    }
    if (meta.opt.req_ip.pres) {
      pkt.push_back(DHCP_OPT_REQ_IP);
      pkt.push_back(DHCP_OPT_REQ_IP_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.req_ip.val); i++) {
        pkt.push_back(meta.opt.req_ip.val.i[i]);
      }
    }
    if (meta.opt.dhcp_srv_id.pres) {
      pkt.push_back(DHCP_OPT_DHCP_SRV_ID);
      pkt.push_back(DHCP_OPT_DHCP_SRV_ID_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.dhcp_srv_id.val); i++) {
        pkt.push_back(meta.opt.dhcp_srv_id.val.i[i]);
      }
    }
    if (meta.opt.dhcp_cli_id.pres) {
      pkt.push_back(DHCP_OPT_DHCP_CLI_ID);
      pkt.push_back(DHCP_OPT_DHCP_CLI_ID_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.dhcp_cli_id.val); i++) {
        pkt.push_back(meta.opt.dhcp_cli_id.val[i]);
      }
    }
    if (meta.opt.hostname.pres) {
      pkt.push_back(DHCP_OPT_HOSTNAME);
      pkt.push_back(meta.opt.hostname.len);
      for (size_t i = 0; i < meta.opt.hostname.len; i++) {
        pkt.push_back(meta.opt.hostname.val[i]);
      }
    }
    if (meta.opt.router.pres) {
      pkt.push_back(DHCP_OPT_ROUTER);
      pkt.push_back(DHCP_OPT_ROUTER_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.router.val); i++) {
        pkt.push_back(meta.opt.router.val.i[i]);
      }
    }
    if (meta.opt.dns.pres) {
      pkt.push_back(DHCP_OPT_DNS);
      pkt.push_back(DHCP_OPT_DNS_LEN);
      for (size_t i = 0; i < sizeof(meta.opt.dns.val); i++) {
        pkt.push_back(meta.opt.dns.val.i[i]);
      }
    }
    if (meta.opt.domain_name.pres) {
      pkt.push_back(DHCP_OPT_DOMAIN_NAME);
      pkt.push_back(meta.opt.domain_name.len);
      for (size_t i = 0; i < meta.opt.domain_name.len; i++) {
        pkt.push_back(meta.opt.domain_name.val[i]);
      }
    }
    if (meta.opt.fqdn.pres) {
      pkt.push_back(DHCP_OPT_FQDN);
      pkt.push_back(meta.opt.fqdn.len);
      pkt.push_back(meta.opt.fqdn.flags);
      pkt.push_back(meta.opt.fqdn.rcode1);
      pkt.push_back(meta.opt.fqdn.rcode2);
      for (size_t i = 0; i < meta.opt.fqdn.len - 3; i++) {
        pkt.push_back(meta.opt.fqdn.str[i]);
      }
    }
    if (meta.opt.end.pres) {
      pkt.push_back(DHCP_OPT_END);
    }
  }

