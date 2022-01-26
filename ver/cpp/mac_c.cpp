#include "../hdr/mac_c.h"

  mac_c::mac_c () {
    
  };

  mac_c::mac_c (
    const mac_addr_t _mac_addr,
    const bool&      _verbose
  ) { 
    mac_addr = _mac_addr;
    verbose = _verbose;
    gen_crc_table(crc_tbl);
  }

  mac_c::~mac_c() {

  }

  bool mac_c::is_broadcast (mac_c::mac_addr_t mac) {
    for (size_t i = 0; i < sizeof(mac_c::mac_addr_t); i++) {
      if (mac.m[i] != 0xff) return false; 
    }
    return true;
  }

  bool mac_c::is_zero (mac_c::mac_addr_t mac) {
    for (size_t i = 0; i < sizeof(mac_c::mac_addr_t); i++) {
      if (mac.m[i] != 0x00) return false; 
    }
    return true;
  }

  bool mac_c::check_pre (std::vector<uint8_t> pkt) {
    return (
      (pkt[0] == 0x55) &&
      (pkt[1] == 0x55) &&
      (pkt[2] == 0x55) &&
      (pkt[3] == 0x55) &&
      (pkt[4] == 0x55) &&
      (pkt[5] == 0x55) &&
      (pkt[6] == 0x55) &&
      (pkt[7] == 0xd5)
    );
  }

  bool mac_c::check_fcs (std::vector<uint8_t> pkt, uint32_t& crc) {
    crc = 0xffffffff;
    for (size_t i = 8; i < pkt.size(); i++) {
			crc = crc_tbl[(crc ^ pkt[i]) & 0xff] ^ (crc >> 8);
    }
    return (crc == CRC_MAGIC_NUMBER);
  }

  uint32_t mac_c::gen_fcs (std::vector<uint8_t> pkt) {
    uint32_t crc = 0xffffffff;
    for (size_t i = 0; i < pkt.size(); i++) {
			crc = crc_tbl[(crc ^ pkt[i]) & 0xff] ^ (crc >> 8);
    }
    return crc;
  }

  void mac_c::gen_crc_table (uint32_t (&tbl) [256]) {
    for (uint32_t i = 0; i < 256; i++) {
      uint32_t cur = i;
      for (int j = 0; j < 8;j++) {
        cur = (cur & 1) ? (cur >> 1) ^ CRC_POLY : cur >> 1; 
      }
      tbl[i] = cur;
    }
  }

  uint16_t mac_c::extract_16 (std::vector<uint8_t> pkt, int idx) {
    return (pkt[idx+1] | (pkt[idx] << 8));
  }

  uint32_t mac_c::extract_32 (std::vector<uint8_t> pkt, int idx) {
    return (pkt[idx+3] | (pkt[idx+2] << 8) | (pkt[idx+1] << 16) | (pkt[idx] << 24));
  }

  mac_c::mac_addr_t mac_c::extract_mac (std::vector<uint8_t> pkt, int idx) {
    mac_addr_t mac;
    for (int i = 0; i < 6; i++) mac.m[i] = pkt[idx+i];
    return mac;
  }

  bool mac_c::eth_parse (std::vector<uint8_t>& pkt, mac_c::mac_hdr_t& hdr) {
    uint32_t crc;
    if (!check_fcs(pkt, crc)) {
      printf("[tb]<- Frame check sequence incorrect: should be %x, received %x\n",
        crc,
        extract_32(pkt, pkt.size()-4)
      );
      return false;
    }

    hdr.dst_mac   = extract_mac(pkt, 8 );
    hdr.src_mac   = extract_mac(pkt, 14);
    hdr.ethertype = extract_16 (pkt, 20);

    pkt = {pkt.begin() + MAC_OFFSET, pkt.end()-4};
    if (verbose) {
      printf("[tb]<- Source: %02x-%02x-%02x-%02x-%02x-%02x. Destination: %02x-%02x-%02x-%02x-%02x-%02x. Ethertype: %04x\n", 
        hdr.src_mac.m[0],
        hdr.src_mac.m[1], 
        hdr.src_mac.m[2], 
        hdr.src_mac.m[3], 
        hdr.src_mac.m[4], 
        hdr.src_mac.m[5],
        hdr.dst_mac.m[0],
        hdr.dst_mac.m[1], 
        hdr.dst_mac.m[2], 
        hdr.dst_mac.m[3], 
        hdr.dst_mac.m[4], 
        hdr.dst_mac.m[5],
        hdr.ethertype
      );
    }
    if ((hdr.dst_mac == mac_addr) || (is_broadcast(hdr.dst_mac))) return true;
    return false;
  }

  bool mac_c::eth_generate (std::vector<uint8_t>& pkt, mac_hdr_t& hdr) {
  
    pkt.insert (pkt.begin(), {
      hdr.dst_mac.m[0],
      hdr.dst_mac.m[1],
      hdr.dst_mac.m[2],
      hdr.dst_mac.m[3],
      hdr.dst_mac.m[4],
      hdr.dst_mac.m[5],
      hdr.src_mac.m[0],
      hdr.src_mac.m[1],
      hdr.src_mac.m[2],
      hdr.src_mac.m[3],
      hdr.src_mac.m[4],
      hdr.src_mac.m[5],
     (uint8_t)(hdr.ethertype >> 8 & 0xff),
     (uint8_t)(hdr.ethertype & 0xff)
    });
    uint32_t fcs = gen_fcs(pkt);
    pkt.insert (pkt.begin(), {
      0x55,
      0x55,
      0x55,
      0x55,
      0x55,
      0x55,
      0x55,
      0xd5
    });
    for (size_t i = 0; i < sizeof(uint32_t); i++) pkt.push_back((uint8_t)(fcs >> 8*i ^ 0xff));
    if (verbose) {
      printf("[tb]-> Destination MAC: %02x-%02x-%02x-%02x-%02x-%02x\n", 
        hdr.dst_mac.m[0],
        hdr.dst_mac.m[1], 
        hdr.dst_mac.m[2], 
        hdr.dst_mac.m[3], 
        hdr.dst_mac.m[4], 
        hdr.dst_mac.m[5]
      );
      printf("[tb]-> Source MAC: %02x-%02x-%02x-%02x-%02x-%02x\n", 
        hdr.src_mac.m[0],
        hdr.src_mac.m[1], 
        hdr.src_mac.m[2], 
        hdr.src_mac.m[3], 
        hdr.src_mac.m[4], 
        hdr.src_mac.m[5]
      );
      printf("[tb]-> Ethertype: %04x\n", hdr.ethertype);
    }
    return true;
  }
