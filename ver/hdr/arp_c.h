#ifndef ARP_C_H
#define ARP_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>
#include "../hdr/mac_c.h"

class arp_c : virtual public mac_c {
  public :
  
    arp_c ();
    ~arp_c ();

    struct arp_hdr_t {
      uint16_t   htype;
      uint16_t   ptype;
      uint8_t    hlen;
      uint8_t    plen;
      uint16_t   opcode;
      mac_addr_t sha;
      uint32_t   spa;
      mac_addr_t tha;
      uint32_t   tpa;
    };

    bool arp_parse    (std::vector<uint8_t> pkt, arp_hdr_t& hdr);
    bool arp_generate (std::vector<uint8_t> pkt, arp_hdr_t& hdr);
};

#endif