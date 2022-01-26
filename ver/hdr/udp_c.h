#ifndef UDP_C_H
#define UDP_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>
#include "../hdr/ipv4_c.h"

class udp_c : virtual public ipv4_c {

  public : 
    
    udp_c ();
    udp_c (bool _verbose);
    ~udp_c ();
    
    static const int UDP_OFFSET = 8;
    bool verbose;
    
    struct udp_hdr_t {
      uint16_t src_port;
      uint16_t dst_port;
      uint16_t length;
      uint16_t checksum;
    };

    bool udp_parse    (
      std::vector<uint8_t>& pkt,
      udp_hdr_t& hdr
    );

    bool udp_generate (
      std::vector<uint8_t>& pkt,
      udp_hdr_t& hdr
    );

};

#endif