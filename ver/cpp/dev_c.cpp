#include "../hdr/dev_c.h"

// top-level DUT interface

dev_c::dev_c(
  const ipv4_c::ipv4_t    _ipv4_addr,
  const ipv4_c::ipv4_t    _subnet_mask,
  const mac_c::mac_addr_t _mac_addr,
  const bool              _mac_verbose,
  const bool              _ipv4_verbose,
  const bool              _arp_verbose,
  const bool              _icmp_verbose,
  const bool              _udp_verbose,
  const bool              _dhcp_verbose
) {
 dhcp = new dhcp_c (
    _ipv4_addr,
    _mac_addr,
    _subnet_mask,
    _ipv4_addr,
    "test_hn",
    "test_dn",
    _dhcp_verbose,
    _udp_verbose,
    _ipv4_verbose,
    _mac_verbose
  );
  arp = new arp_c (
    _mac_addr,
    _ipv4_addr,
    _arp_verbose,
    _mac_verbose
  );
  icmp = new icmp_c (
    _ipv4_addr,
    _mac_addr,
    _icmp_verbose,
    _ipv4_verbose,
    _mac_verbose
  );
  pcap_log = new pcap (
    "log/log.pcap",
    8
  );
  ip_addr        = _ipv4_addr   ;
  subnet_mask    = _subnet_mask ;
  mac_addr       = _mac_addr    ;
  IPV4_BROADCAST = {0xff, 0xff, 0xff, 0xff};
  fsm_tx         = idle_s;
  ifg_ctr        = 0;
}

dev_c::~dev_c() {
  printf("destructor\n");
  pcap_log->~pcap();
}

uint32_t dev_c::ipv4_to_uint32 (const ipv4_c::ipv4_t& ipv4) {
  return (uint32_t)(ipv4.i[0] << 24 | (ipv4.i[1] << 16) | (ipv4.i[2] << 8) | (ipv4.i[3]));
}

bool dev_c::process_rx (char& dat, bool& val) {
  if (!val && (pkt_rx.size() > 0)) {
    pcap_log->write_pkt(cur_tim, pkt_rx);
    //pkt_queue_tx.push(pkt_rx);
    return 1;
  }
  else if (val) pkt_rx.push_back(dat);
  return 0;
}

bool dev_c::process_tx (char& dat, bool& val) {
  switch (fsm_tx) {
    case (idle_s) : {
      ifg_ctr = 0;
      tx_ptr = 0;
      val = 0;
      dat = 0;
      if (!pkt_queue_tx.empty()) {
        fsm_tx = tx_s;
        pkt_tx = pkt_queue_tx.front();
        pkt_queue_tx.pop();
        pcap_log->write_pkt(cur_tim, pkt_tx);
      }
      return false;
      break;
    }
    case (tx_s) : {
      val = 1;
      dat = pkt_tx[tx_ptr++];
      if (tx_ptr == pkt_tx.size()) {
        fsm_tx = ifg_s;
        pkt_tx.clear();
      }
      return false;
      break;
    }
    case (ifg_s) : {
      val = 0;
      ifg_ctr++;
      if (ifg_ctr == IFG_TICKS) {
        fsm_tx = idle_s;
        return true;
      }
      break;
    }
  }
}

std::vector <uint8_t> pkt_to_send;

void dev_c::process (
  char     dat_rx,
  bool     val_rx,
  char&    dat_tx,
  bool&    val_tx,
  unsigned tim
) {
  cur_tim = tim;
  bool pkt_sent     = dev_c::process_tx (dat_tx, val_tx);
  bool pkt_received = dev_c::process_rx (dat_rx, val_rx);
  bool dhcp_send;
  bool arp_send;
  bool icmp_send;

  dhcp->dhcp_process (pkt_rx, pkt_received, pkt_to_send, dhcp_send);
  if (dhcp_send) {
    pkt_queue_tx.push(pkt_to_send);
    pkt_to_send.clear();
  }
  arp->arp_process   (pkt_rx, pkt_received, pkt_to_send, arp_send);
  if (arp_send) {
    pkt_queue_tx.push(pkt_to_send);
    pkt_to_send.clear();
  }
  icmp->icmp_process (pkt_rx, pkt_received, pkt_to_send, icmp_send);
  if (icmp_send) {
    pkt_queue_tx.push(pkt_to_send);
    pkt_to_send.clear();

    return;
  }
  if (pkt_received) pkt_rx.clear();
 // if (pkt_sent) pkt_tx.clear();
}
