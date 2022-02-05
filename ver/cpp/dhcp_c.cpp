#include "../hdr/dhcp_c.h"

  dhcp_c::dhcp_c() {

  }

  dhcp_c::dhcp_c (
    ipv4_t      _ipv4_addr,
    mac_addr_t  _mac_addr,
    ipv4_t      _subnet_mask,
    ipv4_t      _router_addr,
    std::string _hostname,
    std::string _domain_name,
    bool        _verbose,
    bool        _udp_verbose,
    bool        _ipv4_verbose,
    bool        _mac_verbose
  ) : 
    udp_c  (
      _udp_verbose
    ),
    ipv4_c (
      _ipv4_verbose
    ),
    mac_c  (
      _mac_addr,
      _mac_verbose
    )
  {
    state = idle;
    verbose         = _verbose;
    ipv4_addr       = _ipv4_addr;
    mac_addr        = _mac_addr;
    subnet_mask     = _subnet_mask;
    router_addr     = _router_addr;
    dev_hostname    = _hostname;
    dev_domain_name = _domain_name;
  }

  dhcp_c::~dhcp_c() {

  }

  bool dhcp_c::dhcp_parse (std::vector<uint8_t>& pkt, dhcp_c::dhcp_meta_t& meta) {
    if (!(mac_c::eth_parse (pkt, meta.mac_hdr))) 
      return false;
    if (!mac_c::is_broadcast(meta.mac_hdr.dst_mac)) 
      return false;
    if (!(ipv4_c::ipv4_parse(pkt, meta.ipv4_hdr))) 
      return false;
    if (!((meta.ipv4_hdr.dst_ip == ipv4_addr) || ipv4_c::is_broadcast(meta.ipv4_hdr.dst_ip))) 
      return false;
    if (!(udp_c::udp_parse (pkt,  meta.udp_hdr)))
      return false;
    if (!((meta.udp_hdr.src_port == 68) && (meta.udp_hdr.dst_port == 67)))
      return false;
    meta.dhcp_hdr = {0};
    meta.dhcp_hdr.op    = pkt[DHCP_OP_OFFSET   ];
    meta.dhcp_hdr.htype = pkt[DHCP_HTYPE_OFFSET];
    meta.dhcp_hdr.hlen  = pkt[DHCP_HLEN_OFFSET ];
    meta.dhcp_hdr.hops  = pkt[DHCP_HOPS_OFFSET ];
    meta.dhcp_hdr.xid   = extract_32(pkt, DHCP_XID_OFFSET  );
    meta.dhcp_hdr.secs  = extract_16(pkt, DHCP_SECS_OFFSET );
    meta.dhcp_hdr.flags = extract_16(pkt, DHCP_FLAGS_OFFSET);
    meta.dhcp_hdr.claddr = extract_ip(pkt, DHCP_CLADDR_OFFSET);
    meta.dhcp_hdr.yiaddr = extract_ip(pkt, DHCP_YIADDR_OFFSET);
    meta.dhcp_hdr.siaddr = extract_ip(pkt, DHCP_SIADDR_OFFSET);
    meta.dhcp_hdr.giaddr = extract_ip(pkt, DHCP_GIADDR_OFFSET);

    for (size_t i = 0; i < sizeof(chaddr_t); i++) meta.dhcp_hdr.chaddr.val[i] = pkt[DHCP_CHADDR_OFFSET + i];
    for (size_t i = 0; i < sizeof(sname_t); i++)  meta.dhcp_hdr.sname.val[i]  = pkt[DHCP_SNAME_OFFSET  + i];
    for (size_t i = 0; i < sizeof(bootfn_t); i++) meta.dhcp_hdr.file.val[i]   = pkt[DHCP_FILE_OFFSET   + i];
    if (extract_32(pkt, DHCP_COOKIE_OFFSET) != DHCP_COOKIE) printf("[tb] Bad DHCP cookie\n");

    // options
    uint8_t opt_len;
    dhcp_opt_t cur_opt;
    dhcp_field_t field = kind;
    for (size_t i = DHCP_OPTIONS_OFFSET; i < (pkt.size() - FCS_BYTES); i++) {
      switch (field) {
        case (kind) :
          switch (pkt[i]) {
            case (DHCP_OPT_MSG_TYPE) :
              field = length;
              cur_opt = msg_type;
              meta.dhcp_opt.msg_type.pres = 1;
            break;
            case (DHCP_OPT_NET_MASK) :
              field = length;
              cur_opt = net_mask;
              meta.dhcp_opt.net_mask.pres = 1;
            break;
            case (DHCP_OPT_RENEW_TIME) :
              field = length;
              cur_opt = renew_time; 
              meta.dhcp_opt.renew_time.pres = 1;
            break;
            case (DHCP_OPT_REBIND_TIME) :
              field = length;
              cur_opt = rebind_time;
              meta.dhcp_opt.rebind_time.pres = 1;
            break;
            case (DHCP_OPT_LEASE_TIME) :
              field = length;
              cur_opt = lease_time;  
              meta.dhcp_opt.lease_time.pres = 1;
            break;
            case (DHCP_OPT_REQ_IP) :
              field = length;
              cur_opt = req_ip;  
              meta.dhcp_opt.req_ip.pres = 1;
              break;            
            case (DHCP_OPT_DHCP_CLI_ID) :
              field = length;
              cur_opt = dhcp_cli_id;
              meta.dhcp_opt.dhcp_cli_id.pres = 1;
            break;
            case (DHCP_OPT_DHCP_SRV_ID) :
              field = length;
              cur_opt = dhcp_srv_id;
              meta.dhcp_opt.dhcp_srv_id.pres = 1;
            break;
            case (DHCP_OPT_ROUTER) :
              field = length;
              cur_opt = router;
              meta.dhcp_opt.router.pres = 1;
            break;
            case (DHCP_OPT_DNS) :
              field = length;
              cur_opt = dns;
              meta.dhcp_opt.dns.pres = 1;
            break;
            case (DHCP_OPT_DOMAIN_NAME) :
              field = length;
              cur_opt = domain_name;
              meta.dhcp_opt.domain_name.pres = 1;
            break;
            case (DHCP_OPT_FQDN) :
              field = length;
              cur_opt = fqdn;
              meta.dhcp_opt.fqdn.pres = 1;
            break;
            case (DHCP_OPT_HOSTNAME) :
              field = length;
              cur_opt = hostname;
              meta.dhcp_opt.hostname.pres = 1;
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
              printf("[dhcp]<- Unknown option type %x\n", pkt[i]);
              field = length;
            break;
          }
        break;
        case (length) :
          opt_len = pkt[i];
          switch (cur_opt) {
            case (hostname) :
              meta.dhcp_opt.hostname.len = opt_len; 
            break;
            case (domain_name) :
              meta.dhcp_opt.domain_name.len = opt_len; 
            break;
            case (fqdn) :
              meta.dhcp_opt.fqdn.len = opt_len;
            break;
            default :
            break;
          }
          field = (opt_len == 0) ? kind : data;
        break;
        case (data) :
          field = kind;
          switch (cur_opt) {
            case (msg_type) :
              meta.dhcp_opt.msg_type.val = pkt[i];
            break;  
            case (net_mask) :
              meta.dhcp_opt.net_mask.val = extract_ip(pkt, i);
              i = i + 3;
            break;
            case (renew_time) :
              meta.dhcp_opt.renew_time.val = extract_32(pkt, i);
              i = i + 3;
            break;  
            case (rebind_time) :
              meta.dhcp_opt.rebind_time.val = extract_32(pkt, i);
              i = i + 3;
            break;  
            case (lease_time) :
              meta.dhcp_opt.lease_time.val = extract_32(pkt, i);
              i = i + 3;
            break;  
            case (req_ip) :
              meta.dhcp_opt.req_ip.val = extract_ip(pkt, i);
              i = i + 3;
            break;
            case (dhcp_srv_id) :
              meta.dhcp_opt.dhcp_srv_id.val = extract_ip(pkt, i);
              i = i + 3;
            break;  
            case (dhcp_cli_id) :
              for (uint8_t j = 0; j < opt_len; j++) {
                meta.dhcp_opt.dhcp_cli_id.val[j] = pkt[i++];
              }
              i--;
            break;
            case (hostname) :
              for (uint8_t j = 0; j < opt_len; j++) {
                meta.dhcp_opt.hostname.val[j] = pkt[i++];
              }
              i--;
            break;  
            case (router) :
              meta.dhcp_opt.dhcp_srv_id.val = extract_ip(pkt, i);
              i = i + 3;
            break;
            case (dns) :
              meta.dhcp_opt.dns.val = extract_ip(pkt, i);
              i = i + 3;
            break;  
            case (domain_name) :
              for (uint8_t j = 0; j < opt_len; j++) {
                meta.dhcp_opt.domain_name.val[j] = pkt[i++];
              }
              i--;
            break;
            case (fqdn) :
              for (uint8_t j = 0; j < sizeof(fqdn_t); j++) {
                switch (j) {
                  case (0) :
                    meta.dhcp_opt.fqdn.flags  = pkt[i];
                  break;
                  case (1) :
                    meta.dhcp_opt.fqdn.rcode1 = pkt[i];
                  break;
                  case (2) :
                    meta.dhcp_opt.fqdn.rcode2 = pkt[i];
                  break;
                  default :
                    for (uint8_t j = 0; j < opt_len-3; j++) {
                      meta.dhcp_opt.fqdn.str[j] = pkt[3+i++];
                    }
                    i--;
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

  mac_c::mac_addr_t dhcp_c::mac_from_chaddr (chaddr_t chaddr) {
    mac_addr_t mac;
    for (int i = 0; i < 6; i++) {
      mac.m[i] = chaddr.val[i];
    }
    return mac;
  }

  void dhcp_c::dhcp_generate (dhcp_meta_t& meta, std::vector<uint8_t>& pkt) {
    // assemble dhcp header
      pkt.push_back(meta.dhcp_hdr.op);
      pkt.push_back(meta.dhcp_hdr.htype);
      pkt.push_back(meta.dhcp_hdr.hlen);
      pkt.push_back(meta.dhcp_hdr.hops);
      for (size_t i = 0; i < sizeof(uint32_t); i++) pkt.push_back((uint8_t)(meta.dhcp_hdr.xid   >> (sizeof(uint32_t)-1-i)*8));
      for (size_t i = 0; i < sizeof(uint16_t); i++) pkt.push_back((uint8_t)(meta.dhcp_hdr.secs  >> (sizeof(uint16_t)-1-i)*8));
      for (size_t i = 0; i < sizeof(uint16_t); i++) pkt.push_back((uint8_t)(meta.dhcp_hdr.flags >> (sizeof(uint16_t)-1-i)*8));
      for (size_t i = 0; i < sizeof(ipv4_t);   i++) pkt.push_back(meta.dhcp_hdr.claddr.i  [i]);
      for (size_t i = 0; i < sizeof(ipv4_t);   i++) pkt.push_back(meta.dhcp_hdr.yiaddr.i  [i]);
      for (size_t i = 0; i < sizeof(ipv4_t);   i++) pkt.push_back(meta.dhcp_hdr.siaddr.i  [i]);
      for (size_t i = 0; i < sizeof(ipv4_t);   i++) pkt.push_back(meta.dhcp_hdr.giaddr.i  [i]);
      for (size_t i = 0; i < sizeof(chaddr_t); i++) pkt.push_back(meta.dhcp_hdr.chaddr.val[i]);
      for (size_t i = 0; i < sizeof(sname_t);  i++) pkt.push_back(meta.dhcp_hdr.sname.val [i]);
      for (size_t i = 0; i < sizeof(bootfn_t); i++) pkt.push_back(meta.dhcp_hdr.file.val  [i]);
      for (size_t i = 0; i < sizeof(uint32_t); i++) pkt.push_back((uint8_t)(DHCP_COOKIE    >> (sizeof(uint32_t)-1-i)*8));
  
    // assemble dhcp options
    if (meta.dhcp_opt.msg_type.pres) {
      pkt.push_back(DHCP_OPT_MSG_TYPE);
      pkt.push_back(DHCP_OPT_MSG_TYPE_LEN);
      pkt.push_back(meta.dhcp_opt.msg_type.val);
    }
    if (meta.dhcp_opt.net_mask.pres) {
      pkt.push_back(DHCP_OPT_NET_MASK);
      pkt.push_back(DHCP_OPT_NET_MASK_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.net_mask.val); i++) {
        pkt.push_back(meta.dhcp_opt.net_mask.val.i[i]);
      }
    }
    if (meta.dhcp_opt.renew_time.pres) {
      pkt.push_back(DHCP_OPT_RENEW_TIME);
      pkt.push_back(DHCP_OPT_RENEW_TIME_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.renew_time.val); i++) {
        pkt.push_back((uint8_t)(meta.dhcp_opt.renew_time.val >> (sizeof(uint32_t)-1-i)*8));
      }
    }
    if (meta.dhcp_opt.rebind_time.pres) {
      pkt.push_back(DHCP_OPT_REBIND_TIME);
      pkt.push_back(DHCP_OPT_REBIND_TIME_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.rebind_time.val); i++) {
        pkt.push_back((uint8_t)(meta.dhcp_opt.rebind_time.val >> (sizeof(uint32_t)-1-i)*8));
      }
    }
    if (meta.dhcp_opt.lease_time.pres) {
      pkt.push_back(DHCP_OPT_LEASE_TIME);
      pkt.push_back(DHCP_OPT_LEASE_TIME_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.lease_time.val); i++) {
        pkt.push_back((uint8_t)(meta.dhcp_opt.lease_time.val >> (sizeof(uint32_t)-1-i)*8));
      }
    }
    if (meta.dhcp_opt.req_ip.pres) {
      pkt.push_back(DHCP_OPT_REQ_IP);
      pkt.push_back(DHCP_OPT_REQ_IP_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.req_ip.val); i++) {
        pkt.push_back(meta.dhcp_opt.req_ip.val.i[i]);
      }
    }
    if (meta.dhcp_opt.dhcp_srv_id.pres) {
      pkt.push_back(DHCP_OPT_DHCP_SRV_ID);
      pkt.push_back(DHCP_OPT_DHCP_SRV_ID_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.dhcp_srv_id.val); i++) {
        pkt.push_back(meta.dhcp_opt.dhcp_srv_id.val.i[i]);
      }
    }
    if (meta.dhcp_opt.dhcp_cli_id.pres) {
      pkt.push_back(DHCP_OPT_DHCP_CLI_ID);
      pkt.push_back(DHCP_OPT_DHCP_CLI_ID_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.dhcp_cli_id.val); i++) {
        pkt.push_back(meta.dhcp_opt.dhcp_cli_id.val[i]);
      }
    }
    if (meta.dhcp_opt.hostname.pres) {
      pkt.push_back(DHCP_OPT_HOSTNAME);
      pkt.push_back(meta.dhcp_opt.hostname.len);
      for (int i = 0; i < meta.dhcp_opt.hostname.len; i++) {
        pkt.push_back(meta.dhcp_opt.hostname.val[i]);
      }
    }
    if (meta.dhcp_opt.router.pres) {
      pkt.push_back(DHCP_OPT_ROUTER);
      pkt.push_back(DHCP_OPT_ROUTER_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.router.val); i++) {
        pkt.push_back(meta.dhcp_opt.router.val.i[i]);
      }
    }
    if (meta.dhcp_opt.dns.pres) {
      pkt.push_back(DHCP_OPT_DNS);
      pkt.push_back(DHCP_OPT_DNS_LEN);
      for (size_t i = 0; i < sizeof(meta.dhcp_opt.dns.val); i++) {
        pkt.push_back(meta.dhcp_opt.dns.val.i[i]);
      }
    }
    if (meta.dhcp_opt.domain_name.pres) {
      pkt.push_back(DHCP_OPT_DOMAIN_NAME);
      pkt.push_back(meta.dhcp_opt.domain_name.len);
      for (int i = 0; i < meta.dhcp_opt.domain_name.len; i++) {
        pkt.push_back(meta.dhcp_opt.domain_name.val[i]);
      }
    }
    if (meta.dhcp_opt.fqdn.pres) {
      pkt.push_back(DHCP_OPT_FQDN);
      pkt.push_back(meta.dhcp_opt.fqdn.len);
      pkt.push_back(meta.dhcp_opt.fqdn.flags);
      pkt.push_back(meta.dhcp_opt.fqdn.rcode1);
      pkt.push_back(meta.dhcp_opt.fqdn.rcode2);
      for (int i = 0; i < meta.dhcp_opt.fqdn.len - 3; i++) {
        pkt.push_back(meta.dhcp_opt.fqdn.str[i]);
      }
    }
    if (meta.dhcp_opt.end.pres) {
      pkt.push_back(DHCP_OPT_END);
    }
    // Other prococols
    meta.udp_hdr.length = pkt.size()+8;
    udp_c::udp_generate(pkt, meta.udp_hdr);
    ipv4_c::ipv4_generate(pkt, meta.ipv4_hdr);
    mac_c::eth_generate(pkt, meta.mac_hdr);
  }

  // returns true to send pkt_tx
  void dhcp_c::dhcp_process (
    std::vector<uint8_t>  pkt_rx,
    bool                  val_rx,
    std::vector<uint8_t>& pkt_tx,
    bool&                 val_tx
 //   unsigned&    tim
  ) {
  // process lease timers
  val_tx = 0;
  for (int i = 0; i < DHCP_CLIENTS; i++) {
    if (entry[i].status != not_leased) {
      if (entry[i].timer > 0) {
        entry[i].timer--;
      }
      else entry[i].status = not_leased;
    }
  }
  // code below this is only executed
  // when a packet's received
  if (!val_rx) return;
  dhcp_meta_t meta_rx;
  if (!(dhcp_parse (pkt_rx, meta_rx))) {
    return;
  }

  if (!meta_rx.dhcp_opt.msg_type.pres) {
    printf("[dhcp]<- packet without Message Type option\n");
    return;
  }
  if (meta_rx.dhcp_hdr.htype != 0x01) {
    printf("[dhcp]<- Hardware type is not 1 (Ethernet), but %d \n", meta_rx.dhcp_hdr.htype);
    //return;
  }    
  if (meta_rx.dhcp_hdr.hlen != 0x06) {
    printf("[dhcp]<- Hardware address Length is not 6 (Ethernet), but %d \n", meta_rx.dhcp_hdr.hlen);
    return;
  }
    dhcp_meta_t meta_tx = {0};
    bool found = false;
    // set headers
    meta_tx.udp_hdr.dst_port  = 68;
    meta_tx.udp_hdr.src_port  = 67;
    meta_tx.udp_hdr.length    = 0; // will be overwritten in dhcp_generate
    meta_tx.ipv4_hdr.ver      = 4;
    meta_tx.ipv4_hdr.ihl      = 5;
    meta_tx.ipv4_hdr.qos      = 0;
    meta_tx.ipv4_hdr.len      = 0;
    meta_tx.ipv4_hdr.id       = 0;
    meta_tx.ipv4_hdr.frag     = 0;
    meta_tx.ipv4_hdr.ttl      = 64;
    meta_tx.ipv4_hdr.proto    = ipv4_c::UDP;
    meta_tx.ipv4_hdr.checksum = 0; // skip the calculation for now
    meta_tx.ipv4_hdr.src_ip   = {0,   0,   0,   0};
    meta_tx.ipv4_hdr.dst_ip   = {255, 255, 255, 255};
    meta_tx.mac_hdr.dst_mac   = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
    meta_tx.mac_hdr.src_mac   = mac_addr;
    meta_tx.mac_hdr.ethertype = mac_c::IPV4;

    meta_tx.dhcp_hdr.htype    = 1;
    meta_tx.dhcp_hdr.hlen     = 6;
    meta_tx.dhcp_hdr.hops     = 0;
    meta_tx.dhcp_hdr.secs     = 0;
    meta_tx.dhcp_hdr.flags    = 0x8000;

    meta_tx.dhcp_hdr.cookie   = DHCP_COOKIE;

    switch (meta_rx.dhcp_opt.msg_type.val) {
      case (DHCP_MSG_TYPE_DISCOVER) : {
        if (verbose) printf("[dhcp]<- DHCP Discover from %x:%x:%x:%x:%x:%x requesting %d:%d:%d:%d [xid %x] \n",
          meta_rx.mac_hdr.src_mac.m[0],
          meta_rx.mac_hdr.src_mac.m[1],
          meta_rx.mac_hdr.src_mac.m[2],
          meta_rx.mac_hdr.src_mac.m[3],
          meta_rx.mac_hdr.src_mac.m[4],
          meta_rx.mac_hdr.src_mac.m[5],
          meta_rx.dhcp_opt.req_ip.val.i[0],
          meta_rx.dhcp_opt.req_ip.val.i[1],
          meta_rx.dhcp_opt.req_ip.val.i[2],
          meta_rx.dhcp_opt.req_ip.val.i[3],
          meta_rx.dhcp_hdr.xid
        );
        // First attempt to determine whether this is an old client
        // attemmeting to rebind with same xid and chaddr
        for (int i = 0; i < DHCP_CLIENTS; i++) {
          if ((entry[i].status != not_leased) &&
              (entry[i].xid == meta_rx.dhcp_hdr.xid) &&
              (entry[i].mac == mac_from_chaddr(meta_rx.dhcp_hdr.chaddr)))
          {
            entry[i].status = offered;
            entry[i].timer  = DORA_TIMEOUT;
            entry[i].xid    = meta_rx.dhcp_hdr.xid;
            found = true;
            break;
          }
        }
        // If no xid related to that client was found, attemt to add the
        // client to the table
        if (!found) {
          for (int i = 0; i < DHCP_CLIENTS; i++) {
            if (entry[i].status == not_leased) {
              entry[i].status = offered;
              entry[i].timer  = DORA_TIMEOUT;
              entry[i].xid    = meta_rx.dhcp_hdr.xid;
              entry[i].mac    = mac_from_chaddr(meta_rx.dhcp_hdr.chaddr);
              break;
            }
            else if (i == (DHCP_CLIENTS-1)) {
              if (verbose) printf("[dhcp] No space for new clients: xid %x \n", meta_rx.dhcp_hdr.xid);
              return; // No space left for new clients
            }
          }
        }

        meta_tx.dhcp_hdr.op               = DHCP_MSG_TYPE_BOOT_REPLY;

        meta_tx.dhcp_hdr.xid              = meta_rx.dhcp_hdr.xid;
        meta_tx.dhcp_hdr.claddr           = {0, 0, 0, 0};
        meta_tx.dhcp_hdr.chaddr           = meta_rx.dhcp_hdr.chaddr;
        meta_tx.dhcp_hdr.yiaddr           = meta_rx.dhcp_opt.req_ip.val; //todo
        meta_tx.dhcp_hdr.siaddr           = ipv4_addr; 
        meta_tx.dhcp_hdr.giaddr           = {0, 0, 0, 0};
        meta_tx.dhcp_hdr.sname            = {0};
        meta_tx.dhcp_hdr.file             = {0};
        meta_tx.dhcp_hdr.cookie           = DHCP_COOKIE;
       
        meta_tx.dhcp_opt.msg_type.val     = DHCP_MSG_TYPE_OFFER;
        meta_tx.dhcp_opt.net_mask.val     = subnet_mask;
        meta_tx.dhcp_opt.renew_time.val   = 10;
        meta_tx.dhcp_opt.rebind_time.val  = 15;
        meta_tx.dhcp_opt.lease_time.val   = 20;
        meta_tx.dhcp_opt.dhcp_srv_id.val  = ipv4_addr;
        meta_tx.dhcp_opt.router.val       = ipv4_addr;
        meta_tx.dhcp_opt.dns.val          = ipv4_addr;

        for (size_t i = 0; i < sizeof(dev_hostname); i++)  
          meta_tx.dhcp_opt.hostname.val[i]    = dev_hostname[i];
        
        for (size_t i = 0; i < sizeof(dev_domain_name); i++)         
          meta_tx.dhcp_opt.domain_name.val[i] = dev_domain_name[i];

        meta_tx.dhcp_opt.hostname.len     = sizeof(dev_hostname);
        meta_tx.dhcp_opt.domain_name.len  = sizeof(dev_domain_name); 
        meta_tx.dhcp_opt.fqdn.len         = MAX_OPT_PLD;

        meta_tx.dhcp_opt.msg_type.pres    = 1;
        meta_tx.dhcp_opt.net_mask.pres    = 1;
        meta_tx.dhcp_opt.renew_time.pres  = 1;
        meta_tx.dhcp_opt.rebind_time.pres = 1;
        meta_tx.dhcp_opt.lease_time.pres  = 1;
        meta_tx.dhcp_opt.req_ip.pres      = 0;
        meta_tx.dhcp_opt.dhcp_srv_id.pres = 0;
        meta_tx.dhcp_opt.router.pres      = 0;
        meta_tx.dhcp_opt.dns.pres         = 0;
        meta_tx.dhcp_opt.hostname.pres    = 0;
        meta_tx.dhcp_opt.domain_name.pres = 1;
        meta_tx.dhcp_opt.fqdn.pres        = 0;
        meta_tx.dhcp_opt.end.pres         = 1;

        if (verbose) printf("[dhcp]-> DHCP Offer %d:%d:%d:%d to %x:%x:%x:%x:%x:%x [xid %x] \n",
          meta_tx.dhcp_hdr.yiaddr.i[0],
          meta_tx.dhcp_hdr.yiaddr.i[1],
          meta_tx.dhcp_hdr.yiaddr.i[2],
          meta_tx.dhcp_hdr.yiaddr.i[3],
          meta_rx.mac_hdr.src_mac.m[0],
          meta_rx.mac_hdr.src_mac.m[1],
          meta_rx.mac_hdr.src_mac.m[2],
          meta_rx.mac_hdr.src_mac.m[3],
          meta_rx.mac_hdr.src_mac.m[4],
          meta_rx.mac_hdr.src_mac.m[5],
          meta_rx.dhcp_hdr.xid
        );
        dhcp_generate(meta_tx, pkt_tx);
        val_tx = true;
        break;
      }
      case (DHCP_MSG_TYPE_REQUEST) : {
        if (verbose) printf ("[dhcp]<- DHCP Request from %x:%x:%x:%x:%x:%x requesting %d:%d:%d:%d [xid %x] \n",
          meta_rx.mac_hdr.src_mac.m[0],
          meta_rx.mac_hdr.src_mac.m[1],
          meta_rx.mac_hdr.src_mac.m[2],
          meta_rx.mac_hdr.src_mac.m[3],
          meta_rx.mac_hdr.src_mac.m[4],
          meta_rx.mac_hdr.src_mac.m[5],
          meta_rx.dhcp_opt.req_ip.val.i[0],
          meta_rx.dhcp_opt.req_ip.val.i[1],
          meta_rx.dhcp_opt.req_ip.val.i[2],
          meta_rx.dhcp_opt.req_ip.val.i[3],
          meta_rx.dhcp_hdr.xid
        );
        for (int i = 0; i < DHCP_CLIENTS; i++) {
          if ((entry[i].xid == meta_rx.dhcp_hdr.xid) &&
              (entry[i].mac == mac_from_chaddr(meta_rx.dhcp_hdr.chaddr)) &&
              (entry[i].status != not_leased) &&
              (entry[i].xid    = meta_rx.dhcp_hdr.xid)) 
          {
            entry[i].status = leased;
            entry[i].ipv4   = meta_rx.dhcp_opt.req_ip.val;
            break;
          }
          else if (i == DHCP_CLIENTS - 1) {
            if (verbose) printf ("[dhcp] Could not find entry for %x:%x:%x:%x:%x:%x requesting %d:%d:%d:%d [xid %x] \n",
              meta_rx.mac_hdr.src_mac.m[0],
              meta_rx.mac_hdr.src_mac.m[1],
              meta_rx.mac_hdr.src_mac.m[2],
              meta_rx.mac_hdr.src_mac.m[3],
              meta_rx.mac_hdr.src_mac.m[4],
              meta_rx.mac_hdr.src_mac.m[5],
              meta_rx.dhcp_opt.req_ip.val.i[0],
              meta_rx.dhcp_opt.req_ip.val.i[1],
              meta_rx.dhcp_opt.req_ip.val.i[2],
              meta_rx.dhcp_opt.req_ip.val.i[3],
              meta_rx.dhcp_hdr.xid
            );
            return;
          } 
        }
        meta_tx.dhcp_hdr.op               = DHCP_MSG_TYPE_BOOT_REPLY;
        meta_tx.dhcp_hdr.xid              = meta_rx.dhcp_hdr.xid;
        meta_tx.dhcp_hdr.flags            = 0x8000;
        meta_tx.dhcp_hdr.claddr           = {0,0,0,0};
        meta_tx.dhcp_hdr.chaddr           = meta_rx.dhcp_hdr.chaddr;
        meta_tx.dhcp_hdr.yiaddr           = meta_rx.dhcp_opt.req_ip.val; //todo
        meta_tx.dhcp_hdr.siaddr           = ipv4_addr; 
        meta_tx.dhcp_hdr.giaddr           = {0}; 
        
        meta_tx.dhcp_opt.msg_type.val     = DHCP_MSG_TYPE_ACK;
        meta_tx.dhcp_opt.net_mask.val     = subnet_mask;
        meta_tx.dhcp_opt.renew_time.val   = 10;
        meta_tx.dhcp_opt.rebind_time.val  = 15;
        meta_tx.dhcp_opt.lease_time.val   = 20;
        meta_tx.dhcp_opt.dhcp_srv_id.val  = ipv4_addr;
        meta_tx.dhcp_opt.router.val       = router_addr;
        meta_tx.dhcp_opt.dns.val          = ipv4_addr;
        for (size_t i = 0; i < sizeof(dev_hostname); i++)              
          meta_tx.dhcp_opt.hostname.val[i] = dev_hostname[i];
        for (size_t i = 0; i < sizeof(dev_domain_name); i++)           
          meta_tx.dhcp_opt.domain_name.val[i] = dev_domain_name[i];
              
        meta_tx.dhcp_opt.hostname.len     = sizeof(dev_hostname);
        meta_tx.dhcp_opt.domain_name.len  = sizeof(dev_domain_name); 
        meta_tx.dhcp_opt.fqdn.len         = MAX_OPT_PLD;

        meta_tx.dhcp_opt.msg_type.pres    = 1;
        meta_tx.dhcp_opt.net_mask.pres    = 1;
        meta_tx.dhcp_opt.renew_time.pres  = 1;
        meta_tx.dhcp_opt.rebind_time.pres = 1;
        meta_tx.dhcp_opt.lease_time.pres  = 1;
        meta_tx.dhcp_opt.dhcp_srv_id.pres = 1;
        meta_tx.dhcp_opt.router.pres      = 1;
        meta_tx.dhcp_opt.dns.pres         = 1;
        meta_tx.dhcp_opt.hostname.pres    = 0;
        meta_tx.dhcp_opt.domain_name.pres = 1;
        meta_tx.dhcp_opt.fqdn.pres        = 0;
        meta_tx.dhcp_opt.end.pres         = 1;
        if (verbose) printf("[dhcp]-> DHCP Acknowledge %d:%d:%d:%d to %x:%x:%x:%x:%x:%x [xid %x] \n",
          meta_tx.dhcp_hdr.yiaddr.i[0],
          meta_tx.dhcp_hdr.yiaddr.i[1],
          meta_tx.dhcp_hdr.yiaddr.i[2],
          meta_tx.dhcp_hdr.yiaddr.i[3],
          meta_rx.mac_hdr.src_mac.m[0],
          meta_rx.mac_hdr.src_mac.m[1],
          meta_rx.mac_hdr.src_mac.m[2],
          meta_rx.mac_hdr.src_mac.m[3],
          meta_rx.mac_hdr.src_mac.m[4],
          meta_rx.mac_hdr.src_mac.m[5],
          meta_rx.dhcp_hdr.xid
        );
        dhcp_generate(meta_tx, pkt_tx);
        val_tx = true;
        break;
      }
      default : {
        printf("[dhcp]<- Unknown message type");
        break;
      }
    }
  }

    bool dhcp_c::check_lease (
      ipv4_c::ipv4_t _ipv4,
      mac_addr_t     _mac
    ) {
      for (int i = 0; i < DHCP_CLIENTS; i++) {
        if (entry[i].status == leased &&
            entry[i].mac    == _mac &&
            entry[i].ipv4   == _ipv4
        ) 
          return true;
      }
      return false;
    }


