#include "../hdr/dev_c.h"
  
  // top-level DUT interface 
dev_c::dev_c(
  const ipv4_c::ipv4_t ip_addr,
  const ipv4_c::ipv4_t subnet_mask,
  const mac_c::mac_addr_t mac_addr,
  const bool ipv4_verbose
) : 
  mac(mac_addr),
  arp(),
  ipv4(ipv4_verbose), 
  icmp(),
  udp(), 
  dhcp(ip_addr, mac_addr, subnet_mask, ip_addr, "test_hn", "test_dn"),
  pcap_log("log/log.pcap", 8) {
  printf("constructor\n");
  fsm_tx = idle_s;
  memset(rxbuf, 0, TXBUF_SIZE);
  memset(txbuf, 0, TXBUF_SIZE);

  IPV4_BROADCAST = {0xff, 0xff, 0xff, 0xff};
  ifg_ctr = 0;
  len_tx = 0;
  ptr_tx = 0;
}

dev_c::~dev_c() {
  printf("destructor\n");
  pcap_log.~pcap();
}

static const int MAC_ADDR_BITS = 48;
static const int IPV4_ADDR_BITS = 32;
static const int PORT_ADDR_BITS = 16;
static const int DATAPATH_BITS  = 8;

long	dev_c::tb2rtls(uint64_t val, int b) {
	long	s;
	s = (val << (sizeof(val)*8-b));
	s >>= (sizeof(val)*8-b);
	return	s;
}

unsigned long dev_c::tb2rtlus(uint64_t val, int b) {
	return val &= (1<<b)-1;
}

bool dev_c::process_rx (char& dat, bool& val) {
  if (!val && (pkt_rx.size() > 0)) return 1;
  else if (val) pkt_rx.push_back(dat);
  return 0;
  }

size_t dev_c::tx_add_pkt (std::vector<uint8_t>& pkt) {
  pkt_queue_tx.push(pkt);
}

bool dev_c::process_tx (char& dat, bool& val) {
  switch (fsm_tx) {
    case (idle_s) : {
      val = 0;
      dat = 0;
      if (!pkt_queue_tx.empty()) {
        fsm_tx = tx_s;
        pkt_tx = pkt_queue_tx.front();
        pkt_queue_tx.pop();
        ptr_tx = 0;
        pcap_log.write_pkt(cur_tim, pkt_tx);
      }
      return false;
      break;
    }
    case (tx_s) : {
      val = 1;
      dat = pkt_tx.back();
      pkt_tx.pop_back();
      if (pkt_tx.empty()) {
        fsm_tx = ifg_s;
        return true;
      }
      break;
    }
    case (ifg_s) : {
      ifg_ctr++;
      if (ifg_ctr == IFG_TICKS) fsm_tx = idle_s;
    }
  }
}

// Parse PKT of length std::vector<uint8_t> pkt, returns detected protocol with PROTO and corresponding header info
bool dev_c::parse (
  std::vector<uint8_t> &pkt, 
  proto_t              &proto,
  mac_c::mac_hdr_t     &mac_hdr,
  ipv4_c::ipv4_hdr_t   &ipv4_hdr,
  arp_c::arp_hdr_t     &arp_hdr,
  udp_c::udp_hdr_t     &udp_hdr,
  dhcp_c::dhcp_meta_t  &dhcp_meta,
  std::vector<uint8_t> &pld

) {
  if (!(mac.eth_parse(pkt, mac_hdr))) return false;
  switch (mac_hdr.ethertype) {
    case (mac_c::IPV4) : {
      bool ipv4_ok = ipv4.ipv4_parse(pkt, ipv4_hdr);
      if (ipv4_c::is_broadcast(ipv4_hdr.dst_ip)) {
        switch (ipv4_hdr.proto) {
          case (ipv4_c::UDP) : {
            proto = proto_udp;
            if (!(udp.udp_parse(pkt, (ipv4_hdr.ihl << 2) + mac_c::MAC_OFFSET, udp_hdr))) break;
            proto = proto_dhcp;
            if ((udp_hdr.src_port == 68) && (udp_hdr.dst_port == 67)) {
              dhcp.dhcp_parse(pkt, mac_c::MAC_OFFSET + (ipv4_hdr.ihl << 2) + udp_c::UDP_OFFSET, dhcp_meta);
            }
            break;
          }
          case (ipv4_c::ICMP) : {
            proto = proto_icmp;
            break;
          }
          default : {

            break;
          }
        }
      }
      break;
    }
    case (mac_c::ARP) : {
      proto = proto_arp;
      //bool arp_ok = arp.parse(pkt, std::vector<uint8_t> pkt, arp_hdr);
      break;
    }
    default : {
      printf("Unsupported ethertype %04x\n", mac_hdr.ethertype);
      break;
    }
  }
}


bool dev_c::process(
  char     dat_rx,
  bool     val_rx,
  char&    dat_tx,
  bool&    val_tx,
  unsigned tim
) {

  size_t pld_len;
  size_t len_tx;
  char* pld;
  // Process incoming bytes
  // Data is stored in rxbu
  bool send = dev_c::process_rx (dat_rx, val_rx);
  dev_c::process_tx (dat_tx, val_tx);
  // If packet received at this tick, parse it
  proto_t             proto_rx;
  mac_c::mac_hdr_t    mac_hdr_rx;
  ipv4_c::ipv4_hdr_t  ipv4_hdr_rx;
  arp_c::arp_hdr_t    arp_hdr_rx;
  udp_c::udp_hdr_t    udp_hdr_rx;
  dhcp_c::dhcp_meta_t dhcp_meta_rx;
  dhcp_c::dhcp_meta_t dhcp_meta_tx;
  switch (proto_rx) {
    proto_dhcp : {
      bool tx_pend = dhcp.dhcp_process (dhcp_meta_rx, dhcp_meta_tx);
      if (tx_pend) {
        std::vector<uint8_t> pkt;
        dhcp.dhcp_generate (dhcp_meta_tx, pkt);
        dev_c::tx_add_pkt(pkt);
    }
  }
  //printf("Parsing packet of size %d\n", pkt_rx.size());
  mac_c::mac_hdr_t   mac_hdr;
  ipv4_c::ipv4_hdr_t ipv4_hdr;
  arp_c::arp_hdr_t   arp_hdr;
  udp_c::udp_hdr_t   udp_hdr;
  dev_c::process_tx(dat_tx, val_tx);
  if (len_rx) pcap_log.write_pkt(1234, rxbuf, len_rx);
  if (len_rx) pcap_log.write_pkt(1234, rxbuf, len_rx);

  return 1;
}
