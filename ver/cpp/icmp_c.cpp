#include "../hdr/icmp_c.h"


  icmp_c::icmp_c() {

  };
  icmp_c::~icmp_c() {
    
  };

  //bool icmp_c::parse (std::vector<uint8_t>& pkt, int offset, udp_c::hdr_t& hdr) {
  //  hdr_t hdr;
  //  hdr.src_port   = extract_16  (pkt, 0  + offset);
  //  hdr.dst_port   = extract_16  (pkt, 2  + offset);
  //  hdr.length     = extract_16  (pkt, 4  + offset);
  //  hdr.checksum   = extract_16  (pkt, 6  + offset);
  //  printf("src %d\n", hdr.src_port);
  //  printf("dst %d\n", hdr.dst_port);    
  //  if (src_port == 0) return false;
  //  if (dst_port == 0) return false;
  //  return true;
  //}
