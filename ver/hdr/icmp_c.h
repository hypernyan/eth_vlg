#ifndef ICMP_C_H
#define ICMP_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>
#include "../hdr/ipv4_c.h"

class icmp_c {

  public : 
    icmp_c();
    ~icmp_c();
    
    struct icmp_hdr_t {

    };

    bool parse (std::vector<uint8_t> pkt, int offset, icmp_hdr_t hdr);

};

#endif