#include "../hdr/ipv4_c.h"
  ipv4_c::ipv4_c () {
  }

  ipv4_c::ipv4_c (bool _verbose) {
    verbose = _verbose;
  //  const ipv4_t IPV4_BROADCAST = {0xff, 0xff, 0xff, 0xff};
  }

  ipv4_c::~ipv4_c () {
  }

  ipv4_c::ipv4_t ipv4_c::extract_ip (std::vector<uint8_t> pkt, int offset) {
    ipv4_t ipv4;
    for (size_t i = 0; i < sizeof(ipv4_t); i++) {
      ipv4.i[i] = pkt[offset+i];
    }
    return ipv4;
  }

  bool ipv4_c::is_broadcast (ipv4_c::ipv4_t& ip) {
    for (size_t i = 0; i < sizeof(ipv4_c::ipv4_t); i++) {
      if (ip.i[i] != 0xff) return false; 
    }
    return true;
  }

  bool ipv4_c::is_zero (ipv4_c::ipv4_t& ip) {
    for (size_t i = 0; i < sizeof(ipv4_c::ipv4_t); i++) {
      if (ip.i[i] != 0x00) return false; 
    }
    return true;
  }

  bool ipv4_c::ipv4_parse (std::vector<uint8_t>& pkt, ipv4_c::ipv4_hdr_t& hdr) {
    hdr.ver      =            pkt [0] >> 4;
    hdr.ihl      =            pkt [0] & 0x0f;
    hdr.qos      =            pkt [1];
    hdr.len      = extract_16(pkt, 2);
    hdr.id       = extract_16(pkt, 4);
    hdr.frag     = extract_16(pkt, 6);
    hdr.ttl      =            pkt [8];
    hdr.proto    =            pkt [9];
    hdr.checksum = extract_16(pkt, 10);
    hdr.src_ip   = extract_ip(pkt, 12);
    hdr.dst_ip   = extract_ip(pkt, 16);

    pkt = {pkt.begin()+IPV4_OFFSET, pkt.end()};
    return true;
  }

  void ipv4_c::ipv4_generate (std::vector<uint8_t>& pkt, ipv4_c::ipv4_hdr_t& hdr) {
    pkt.insert (pkt.begin(), {
      (uint8_t)((hdr.ver << 4) | hdr.ihl),
      hdr.qos,
      (uint8_t)(hdr.len >> 8      & 0xff),
      (uint8_t)(hdr.len           & 0xff),
      (uint8_t)(hdr.id >> 8       & 0xff),
      (uint8_t)(hdr.id            & 0xff),
      (uint8_t)(hdr.frag >> 8     & 0xff),
      (uint8_t)(hdr.frag          & 0xff),
      (uint8_t)(hdr.ttl           & 0xff),
      (uint8_t)(hdr.proto         & 0xff),
      (uint8_t)(hdr.checksum >> 8 & 0xff),
      (uint8_t)(hdr.checksum      & 0xff),
      hdr.src_ip.i[0],
      hdr.src_ip.i[1],
      hdr.src_ip.i[2],
      hdr.src_ip.i[3],
      hdr.dst_ip.i[0],
      hdr.dst_ip.i[1],
      hdr.dst_ip.i[2],
      hdr.dst_ip.i[3]
    });
  }
