#ifndef MAC_C_H
#define MAC_C_H

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <list>
#include <algorithm>
#include <iterator>
#include <iomanip>

class mac_c {

  public :

    static const int N = 2;

    static const int MAC_ADDR_BITS         = 48;
    static const int IPV4_ADDR_BITS        = 32;
    static const int PORT_ADDR_BITS        = 16;
    static const int DATAPATH_BITS         = 8;

    static const uint32_t CRC_POLY         = 0xEDB88320;
    static const uint32_t CRC_MAGIC_NUMBER = 0xDEBB20E3;
    
    // Ethertype
    static const uint16_t IPV4             = 0x0800;
    static const uint16_t ARP              = 0x0806;

    static const int FCS_BYTES       = 4;
    static const int PREAMBLE_BYTES  = 8;
    static const int MAC_ADDR_BYTES  = 6;
    static const int MAC_OFFSET      = 22;

    struct mac_addr_t {
      uint8_t m [MAC_ADDR_BYTES];
    };
    
    mac_addr_t mac_addr; // mac address of class object
    bool verbose;
    std::vector<uint8_t> PREAMBLE{ 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0xd5 };

    struct phy_t {
      bool    err;
      bool    val;
      uint8_t dat;
    };
    
    struct mac_hdr_t {
      uint16_t   ethertype;
      mac_addr_t src_mac;
      mac_addr_t dst_mac;
    };

    uint32_t crc_tbl[256];
    
    mac_c ();

    mac_c (
      const mac_addr_t _mac_addr,
      const bool&      _verbose
    );
    ~mac_c ();

    bool is_broadcast (mac_c::mac_addr_t mac);
    bool is_zero      (mac_c::mac_addr_t mac);

    uint16_t extract_16 (std::vector<uint8_t> pkt, int idx);
    uint32_t extract_32 (std::vector<uint8_t> pkt, int idx);
    mac_addr_t extract_mac (std::vector<uint8_t> pkt, int idx);

    // checks MAC packet's preamble
    bool check_pre (std::vector<uint8_t> pkt);

    // checks MAC packet's FCS
    bool check_fcs (std::vector<uint8_t> pkt, uint32_t& crc);
    uint32_t gen_fcs (std::vector<uint8_t> pkt);
    
    // generates CRC table for FCS calculation
    void gen_crc_table (uint32_t (&tbl)[256]);

    bool eth_parse    (std::vector<uint8_t>& pkt, mac_hdr_t& hdr);
    bool eth_generate (std::vector<uint8_t>& pkt, mac_hdr_t& hdr);

    friend bool operator==(const mac_c::mac_addr_t& lhs, const mac_c::mac_addr_t& rhs) {
      for (size_t i = 0; i < sizeof(mac_c::mac_addr_t); i++) {
        if (lhs.m[i] != rhs.m[i]) return false;
      }
      return true;
    }
  
    friend bool operator==(mac_c::mac_addr_t& lhs, mac_c::mac_addr_t& rhs) {
      for (size_t i = 0; i < sizeof(mac_c::mac_addr_t); i++) {
        if (lhs.m[i] != rhs.m[i]) return false;
      }
      return true;
    }

    friend bool operator!=(const mac_c::mac_addr_t& lhs, const mac_c::mac_addr_t& rhs) {
      for (size_t i = 0; i < sizeof(mac_c::mac_addr_t); i++) {
        if (lhs.m[i] != rhs.m[i]) return true;
      }
      return false;
    }
  
    friend bool operator!=(mac_c::mac_addr_t& lhs, mac_c::mac_addr_t& rhs) {
      for (size_t i = 0; i < sizeof(mac_c::mac_addr_t); i++) {
        if (lhs.m[i] != rhs.m[i]) return true;
      }
      return false;
    }
  private:
};

#endif
