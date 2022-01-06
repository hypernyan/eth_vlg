#ifndef IPV4_C_H
#define IPV4_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>
#include "../hdr/mac_c.h"
//  The ACP client class methods are divied into 
// 1. public -> physical receive/transmit lines with DUT
// 2. private -> methods to process FSM, gather errors, etc.

using namespace std;

class ipv4_c : virtual public mac_c {

  public :

    ipv4_c ();
    ipv4_c (bool verbose);
    ~ipv4_c ();
  
    static const uint8_t ICMP = 1;
    static const uint8_t UDP  = 17;
    static const uint8_t TCP  = 6;
    static const int IPV4_HDR_LEN = 20;
    static const int IPV4_ADDR_BYTES = 4;
    static const int IPV4_OFFSET = 20;

    struct ipv4_t {
      uint8_t i [IPV4_ADDR_BYTES];
    };
    

    
    struct ipv4_hdr_t {
      uint8_t  ver;
      uint8_t  ihl;
      uint8_t  qos;
      uint16_t len;
      uint16_t id;
      uint16_t frag;
      uint8_t  ttl;
      uint8_t  proto;
      uint16_t checksum;
      ipv4_t   src_ip;
      ipv4_t   dst_ip;
    };
    ipv4_t extract_ip (std::vector<uint8_t> pkt, int offset);

    bool ipv4_parse(std::vector<uint8_t>& pkt, ipv4_c::ipv4_hdr_t& hdr);
    void ipv4_generate(std::vector<uint8_t>& pkt, ipv4_c::ipv4_hdr_t& hdr);

    static bool is_broadcast (ipv4_t& ip);
  private : 
    bool VERBOSE = 0;

};

#endif
