#include "../hdr/udp_c.h"
  udp_c::udp_c() {

  };
  udp_c::udp_c(bool _verbose) {
    verbose = _verbose;
  };
  udp_c::~udp_c() {};

  bool udp_c::udp_parse (std::vector<uint8_t>& pkt, udp_c::udp_hdr_t& hdr) {
    hdr.src_port   = extract_16  (pkt, 0);
    hdr.dst_port   = extract_16  (pkt, 2);
    hdr.length     = extract_16  (pkt, 4);
    hdr.checksum   = extract_16  (pkt, 6);
    pkt = {pkt.begin()+UDP_OFFSET, pkt.end()};
    if (hdr.src_port == 0) return false;
    if (hdr.dst_port == 0) return false;
    return true;
  }

  bool udp_c::udp_generate (std::vector<uint8_t>& pkt, udp_c::udp_hdr_t& hdr) {
    pkt.insert (pkt.begin(), {
      (uint8_t)(hdr.src_port >> 8 & 0xff),
      (uint8_t)(hdr.src_port      & 0xff),
      (uint8_t)(hdr.dst_port >> 8 & 0xff),
      (uint8_t)(hdr.dst_port      & 0xff),
      (uint8_t)(hdr.length   >> 8 & 0xff),
      (uint8_t)(hdr.length        & 0xff),
      (uint8_t)(hdr.checksum >> 8 & 0xff),
      (uint8_t)(hdr.checksum      & 0xff),
    });
    if (hdr.src_port == 0) return false;
    if (hdr.dst_port == 0) return false;
    return true;
  }
