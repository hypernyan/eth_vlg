#include "../hdr/arp_c.h"

  arp_c::arp_c (
    mac_c::mac_addr_t _mac_addr, // dev parameters
    ipv4_c::ipv4_t    _ipv4_addr,
    bool              _verbose,
    bool              _mac_verbose
  ) :
    mac_c (
      _mac_addr,
      _mac_verbose
    ) 
  {
    dev_mac = _mac_addr;
    dev_ipv4 = _ipv4_addr;
    verbose = _verbose;
  }

  arp_c::~arp_c () {

  }

  bool arp_c::arp_parse (std::vector<uint8_t>& pkt, arp_c::arp_hdr_t& hdr) {
    mac_hdr_t mac_hdr;
    if (!(mac_c::eth_parse (pkt, mac_hdr)))
      return false;
    if (mac_hdr.ethertype != ARP)
      return false;
    hdr.htype   = extract_16  (pkt, 0);
    hdr.ptype   = extract_16  (pkt, 2);
    hdr.hlen    = pkt[4];
    hdr.plen    = pkt[5];
    hdr.opcode  = extract_16  (pkt, 6);
    hdr.sha     = extract_mac (pkt, 8);
    hdr.spa     = ipv4_c::extract_ip  (pkt, 14);
    hdr.tha     = extract_mac (pkt, 18);
    hdr.tpa     = ipv4_c::extract_ip  (pkt, 24);
    return true;
  }

  void arp_c::arp_generate (std::vector<uint8_t>& pkt, arp_c::arp_hdr_t& hdr) {
    mac_hdr_t mac_hdr;
    pkt.push_back((uint8_t)(hdr.htype  >> 8 & 0xff));
    pkt.push_back((uint8_t)(hdr.htype       & 0xff));
    pkt.push_back((uint8_t)(hdr.ptype  >> 8 & 0xff));
    pkt.push_back((uint8_t)(hdr.ptype       & 0xff));
    pkt.push_back((uint8_t)(hdr.hlen              ));
    pkt.push_back((uint8_t)(hdr.plen              ));
    pkt.push_back((uint8_t)(hdr.opcode >> 8 & 0xff));
    pkt.push_back((uint8_t)(hdr.opcode      & 0xff));
    pkt.push_back((uint8_t)(hdr.sha.m[0]));
    pkt.push_back((uint8_t)(hdr.sha.m[1]));
    pkt.push_back((uint8_t)(hdr.sha.m[2]));
    pkt.push_back((uint8_t)(hdr.sha.m[3]));
    pkt.push_back((uint8_t)(hdr.sha.m[4]));
    pkt.push_back((uint8_t)(hdr.sha.m[5]));
    pkt.push_back((uint8_t)(hdr.spa.i[0]));
    pkt.push_back((uint8_t)(hdr.spa.i[1]));
    pkt.push_back((uint8_t)(hdr.spa.i[2]));
    pkt.push_back((uint8_t)(hdr.spa.i[3]));
    pkt.push_back((uint8_t)(hdr.tha.m[0]));
    pkt.push_back((uint8_t)(hdr.tha.m[1]));
    pkt.push_back((uint8_t)(hdr.tha.m[2]));
    pkt.push_back((uint8_t)(hdr.tha.m[3]));
    pkt.push_back((uint8_t)(hdr.tha.m[4]));
    pkt.push_back((uint8_t)(hdr.tha.m[5]));
    pkt.push_back((uint8_t)(hdr.tpa.i[0]));
    pkt.push_back((uint8_t)(hdr.tpa.i[1]));
    pkt.push_back((uint8_t)(hdr.tpa.i[2]));
    pkt.push_back((uint8_t)(hdr.tpa.i[3]));
    if (hdr.opcode == 1) mac_hdr.dst_mac = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
    if (hdr.opcode == 2) mac_hdr.dst_mac = hdr.tha;
    mac_hdr.src_mac = dev_mac;
    mac_hdr.ethertype = ARP;
    mac_c::eth_generate(pkt, mac_hdr);
  }

  void arp_c::arp_request (
    std::vector<uint8_t>& pkt,
    ipv4_c::ipv4_t ipv4
  ) {
    arp_hdr_t hdr;
    hdr.htype  = 1;
    hdr.ptype  = IPV4;
    hdr.hlen   = 6;
    hdr.plen   = 4;
    hdr.opcode = 1;
    hdr.sha    = dev_mac;
    hdr.spa    = dev_ipv4;
    hdr.tha    = {0};
    hdr.tpa    = ipv4;
    arp_generate (pkt, hdr);
  }

  void arp_c::arp_reply (
    std::vector<uint8_t>& pkt,
    ipv4_c::ipv4_t ipv4,
    mac_c::mac_addr_t mac
  ) {
    arp_hdr_t hdr;
    hdr.htype  = 1;
    hdr.ptype  = IPV4;
    hdr.hlen   = 6;
    hdr.plen   = 4;
    hdr.opcode = 2;
    hdr.sha    = dev_mac;
    hdr.spa    = dev_ipv4;
    hdr.tha    = mac;
    hdr.tpa    = ipv4;
    arp_generate (pkt, hdr);
  }

  void arp_c::arp_process (    
    std::vector<uint8_t>  pkt_rx,
    bool                  val_rx,
    std::vector<uint8_t>& pkt_tx,
    bool&                 val_tx
  ) {
    arp_hdr_t hdr_rx;
    unsigned mac_idx;
    unsigned ipv4_idx;
    val_tx = false;
    // skip processing intenal logic if a packet arrives at this tick
    if (val_rx) {
      if (arp_parse (pkt_rx, hdr_rx)) {
        process_entry(hdr_rx.sha, hdr_rx.spa);
        // if reply received...
        if (hdr_rx.opcode == 1) {
          // ...generate response
          arp_reply(pkt_tx, hdr_rx.spa, hdr_rx.sha);
          val_tx = true;
          return;
        }
      }
    } else {
      arp_hdr_t arp_hdr;
      // scan ARP entries
      for (size_t i = 0; i < entry.size(); i++) {
        if (entry[i].tries == REQUEST_RETRIES) {
          entry.erase(entry.begin() + i);
          return;
        }
        if (entry[i].timer == 0) {
          if (entry[i].transmit_timer-- == 0) {
            entry[i].transmit_timer = TRANSMIT_INTERVAL;
            entry[i].tries++;
            arp_request(pkt_tx, entry[i].ipv4);
            val_tx = true;
            return;
          }
        }
        else entry[i].timer--;
      }
    }
  }

  bool arp_c::find_mac (mac_addr_t& mac, unsigned& idx) {
    for (idx = 0; idx < entry.size(); idx++) {
      if (entry[idx].mac == mac) return true;
    }
    return false;
  }

  bool arp_c::find_ipv4 (ipv4_c::ipv4_t& ipv4, unsigned& idx) {
    for (idx = 0; idx < entry.size(); idx++) {
      if (entry[idx].ipv4 == ipv4) return true;
    }
    return false;
  }

  void arp_c::create_entry (
    ipv4_c::ipv4_t ipv4
  ) {
    entry_t ent;
    ent.mac   = {0};
    ent.ipv4  = ipv4;
    ent.bound = false;
    ent.tries = 0;
    ent.timer = 0;
    ent.transmit_timer = 0;
    entry.push_back(ent);
  }

  void arp_c::process_entry (
    mac_c::mac_addr_t mac,
    ipv4_c::ipv4_t ipv4
  ) {
    unsigned mac_idx, ipv4_idx; 
    bool mac_found =  find_mac  (mac, mac_idx);
    bool ipv4_found = find_ipv4 (ipv4, ipv4_idx);
    if (mac_found && ipv4_found && mac_idx == ipv4_idx) {
      if (verbose) printf("[arp] Entry %x:%x:%x:%x:%x:%x - %d.%d.%d.%d up to date.\n",
        mac.m[0], 
        mac.m[1], 
        mac.m[2], 
        mac.m[3], 
        mac.m[4], 
        mac.m[5],
        ipv4.i[0],
        ipv4.i[1],
        ipv4.i[2],
        ipv4.i[3]
      );
      entry[mac_idx].tries = 0;
      entry[mac_idx].timer = ARP_ENTRY_LIFE;
    }
    else if (mac_found && ipv4_found && mac_idx != ipv4_idx) {
      if (verbose) printf("[arp] Warning: %d.%d.%d.%d was bound to %x:%x:%x:%x:%x:%x; %x:%x:%x:%x:%x:%x was bound to %d.%d.%d.%d.\n",
        ipv4.i[0],
        ipv4.i[1],
        ipv4.i[2],
        ipv4.i[3],
        entry[mac_idx].mac.m[0],
        entry[mac_idx].mac.m[1],
        entry[mac_idx].mac.m[2],
        entry[mac_idx].mac.m[3],
        entry[mac_idx].mac.m[4],
        entry[mac_idx].mac.m[5],
        mac.m[0], 
        mac.m[1], 
        mac.m[2], 
        mac.m[3], 
        mac.m[4], 
        mac.m[5],
        entry[ipv4_idx].ipv4.i[0],
        entry[ipv4_idx].ipv4.i[1],
        entry[ipv4_idx].ipv4.i[2],
        entry[ipv4_idx].ipv4.i[3]
      );
      entry[ipv4_idx].mac = mac;
    }
    else if (mac_found && entry[mac_idx].bound) {
      if (verbose) printf("[arp] %x:%x:%x:%x:%x:%x was bound to %d.%d.%d.%d.\n",
        mac.m[0], 
        mac.m[1], 
        mac.m[2], 
        mac.m[3], 
        mac.m[4], 
        mac.m[5],
        entry[mac_idx].ipv4.i[0],
        entry[mac_idx].ipv4.i[1],
        entry[mac_idx].ipv4.i[2],
        entry[mac_idx].ipv4.i[3]
      );      
      entry[mac_idx].ipv4 = ipv4;
      entry[mac_idx].tries = 0;
      entry[mac_idx].timer = ARP_ENTRY_LIFE;
    }
    else if (ipv4_found) {
      if (entry[ipv4_idx].bound) {
        if (verbose) printf("[arp] %d.%d.%d.%d was bound to %x:%x:%x:%x:%x:%x. New: %x:%x:%x:%x:%x:%x.\n",
          ipv4.i[0],
          ipv4.i[1],
          ipv4.i[2],
          ipv4.i[3],
          entry[ipv4_idx].mac.m[0],
          entry[ipv4_idx].mac.m[1],
          entry[ipv4_idx].mac.m[2],
          entry[ipv4_idx].mac.m[3],
          entry[ipv4_idx].mac.m[4],
          entry[ipv4_idx].mac.m[5],
          mac.m[0],
          mac.m[1],
          mac.m[2],
          mac.m[3],
          mac.m[4],
          mac.m[5]
        );
      } else {
        if (verbose) printf("[arp] %d.%d.%d.%d is now bound to %x:%x:%x:%x:%x:%x.\n",
          ipv4.i[0],
          ipv4.i[1],
          ipv4.i[2],
          ipv4.i[3],
          mac.m[0],
          mac.m[1],
          mac.m[2],
          mac.m[3],
          mac.m[4],
          mac.m[5]
        );        
      }
      entry[ipv4_idx].bound = true;
      entry[ipv4_idx].mac = mac;
      entry[ipv4_idx].tries = 0;
      entry[ipv4_idx].timer = ARP_ENTRY_LIFE;
    }
    else {
      entry_t ent;
      ent.mac   = mac;
      ent.ipv4  = ipv4;
      ent.bound = false;
      ent.tries = 0;
      ent.timer = ARP_ENTRY_LIFE;
      ent.transmit_timer = 0;
      entry.push_back(ent);
    }
  }

  bool arp_c::check (
    mac_c::mac_addr_t mac,
    ipv4_c::ipv4_t ipv4
  ) {
    unsigned mac_idx, ipv4_idx; 
    bool mac_found =  find_mac  (mac,  mac_idx);
    bool ipv4_found = find_ipv4 (ipv4, ipv4_idx);
    return (mac_found && ipv4_found && (mac_idx == ipv4_idx));
  }