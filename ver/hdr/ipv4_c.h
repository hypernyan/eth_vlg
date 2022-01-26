#ifndef IPV4_C_H
#define IPV4_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>
#include "../hdr/mac_c.h"

class ipv4_c : virtual public mac_c {

  public :
    
    ipv4_c ();
    ipv4_c (
      bool _verbose
    );

    ~ipv4_c ();

    // supported protocols
    static const uint8_t ICMP = 1;
    static const uint8_t UDP  = 17;
    static const uint8_t TCP  = 6;
    // 
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
      
    mac_c::mac_addr_t mac_addr;
    ipv4_c::ipv4_t    ipv4_addr;  
    int verbose;

    friend bool operator==(const ipv4_c::ipv4_t& lhs, const ipv4_c::ipv4_t& rhs) {
      for (size_t i = 0; i < sizeof(ipv4_c::ipv4_t); i++) {
        if (lhs.i[i] != rhs.i[i]) return false;
      }
      return true;
    }
  
    friend bool operator==(ipv4_c::ipv4_t& lhs, ipv4_c::ipv4_t& rhs) {
      for (size_t i = 0; i < sizeof(ipv4_c::ipv4_t); i++) {
        if (lhs.i[i] != rhs.i[i]) return false;
      }
      return true;
    }

    friend bool operator!=(const ipv4_c::ipv4_t& lhs, const ipv4_c::ipv4_t& rhs) {
      for (size_t i = 0; i < sizeof(ipv4_c::ipv4_t); i++) {
        if (lhs.i[i] != rhs.i[i]) return true;
      }
      return false;
    }
  
    friend bool operator!=(ipv4_c::ipv4_t& lhs, ipv4_c::ipv4_t& rhs) {
      for (size_t i = 0; i < sizeof(ipv4_c::ipv4_t); i++) {
        if (lhs.i[i] != rhs.i[i]) return true;
      }
      return false;
    }

    // Extract IP address from an offset of a vector pkt 
    static ipv4_t extract_ip (std::vector<uint8_t> pkt, int offset);

    static bool is_broadcast (ipv4_t& ip);
    static bool is_zero      (ipv4_t& ip);
    // Parse IP packet by extracting IPv4 header to hdr and leaving payload at pkt
    bool ipv4_parse    (std::vector<uint8_t>& pkt, ipv4_c::ipv4_hdr_t& hdr);
    // Assemble an IP frame based on payload in pkt and IPv4 header in hdr
    void ipv4_generate (std::vector<uint8_t>& pkt, ipv4_c::ipv4_hdr_t& hdr);
  private :
    bool VERBOSE = 0;

};

#endif
