#ifndef MAC_C_H
#define MAC_C_H

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <list>
#include <algorithm>
#include <iterator>
#include <iomanip>
//  The ACP client class methods are divied into 
// 1. public -> physical receive/transmit lines with DUT
// 2. private -> methods to process FSM, gather errors, etc.


class mac_c {

  public :

    static const int N = 2;

    static const int MAC_ADDR_BITS                  = 48;
    static const int IPV4_ADDR_BITS                 = 32;
    static const int PORT_ADDR_BITS                 = 16;
    static const int DATAPATH_BITS                  = 8;

    static const uint32_t CRC_POLY                  = 0xEDB88320;
    static const uint32_t CRC_MAGIC_NUMBER          = 0xDEBB20E3;
    
    // Ethertype
    static const uint16_t IPV4                      = 0x0800;
    static const uint16_t ARP                       = 0x0806;

    static const int FCS_BYTES       = 4;
    static const int PREAMBLE_BYTES  = 8;
    static const int MAC_ADDR_BYTES  = 6;
    static const int MAC_OFFSET      = 22;

    struct mac_addr_t {
      uint8_t m [MAC_ADDR_BYTES];
    };
    
    mac_addr_t mac_addr; // mac address of class object

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

    // local copy of the interface
    phy_t phy;
    
    std::vector <uint8_t> rx[N];

    mac_c ();
    mac_c (mac_addr_t mac_addr);
    ~mac_c ();

    uint16_t extract_16 (std::vector<uint8_t> pkt, int idx);
    uint32_t extract_32 (std::vector<uint8_t> pkt, int idx);
    mac_addr_t extract_mac (std::vector<uint8_t> pkt, int idx);

    // checks MAC packet's preamble
    bool check_pre (std::vector<uint8_t> pkt);

    // checks MAC packet's FCS
    bool check_fcs (std::vector<uint8_t> pkt);
    uint32_t gen_fcs (std::vector<uint8_t> pkt);
    
    // generates CRC table for FCS calculation
    void gen_crc_table (uint32_t (&tbl)[256]);

    bool eth_parse    (std::vector<uint8_t>& pkt, mac_hdr_t& hdr);
    bool eth_generate (std::vector<uint8_t>& pkt, mac_hdr_t& hdr);

  private:
};

#endif
