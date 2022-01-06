#ifndef DEV_C_H
#define DEV_C_H

#include <stdio.h>
#include <stdlib.h>

#include <queue>
#include <vector>
#include <fstream>
#include <string.h>

#include "../hdr/mac_c.h"
#include "../hdr/dhcp_c.h"
#include "../hdr/arp_c.h"
#include "../hdr/icmp_c.h"
#include "../hdr/dhcp_c.h"
#include "../hdr/ipv4_c.h"
#include "../hdr/pcap.h"

class dev_c {
  public:
     dev_c (
      const ipv4_c::ipv4_t ip_addr,
      const ipv4_c::ipv4_t subnet_mask,
      const mac_c::mac_addr_t mac_addr,
      const bool ipv4_verbose
    );
    ~dev_c ();

    ipv4_c::ipv4_t IPV4_BROADCAST;

    static const size_t   IFG_TICKS  = 20;
    static const unsigned RXBUF_SIZE = 65536;    
    static const unsigned TXBUF_SIZE = 65536;
    typedef enum {
      proto_arp,
      proto_icmp,
      proto_udp,
      proto_tcp,
      proto_dhcp
    } proto_t;

    unsigned cur_tim;
    unsigned tx_ptr;

    unsigned ifg_ctr;
    unsigned rx_idx;
    
    size_t len_tx;
    unsigned ptr_tx;

    // protocol handlers
    mac_c  mac;
    arp_c  arp;
    ipv4_c ipv4;
    icmp_c icmp;
    udp_c  udp;
    dhcp_c dhcp;
    pcap   pcap_log;

    // queue of packets
    std::queue<std::vector<uint8_t>> pkt_queue_tx;
    std::vector<uint8_t> pkt_tx;
    std::vector<uint8_t> pkt_rx;
 
    enum {
      idle_s,
      tx_s,
      ifg_s
    } fsm_tx;

    bool process_rx (char& dat, bool& val);
    void process_tx (char& dat, bool& val);

    size_t tx_add_pkt (
      std::vector<uint8_t>& pkt
    );
    
    bool parse (
      std::vector<uint8_t> &pkt,
      proto_t              &proto,     // detected protocol
      mac_c::mac_hdr_t     &mac_hdr,
      ipv4_c::ipv4_hdr_t   &ipv4_hdr,
      arp_c::arp_hdr_t     &arp_hdr,
      udp_c::udp_hdr_t     &udp_hdr,
      dhcp_c::dhcp_meta_t  &dhcp_meta,
      std::vector<uint8_t> &pld
    );

    bool process (
      char     dat_rx,
      bool     val_rx,
      char&    dat_tx,
      bool&    val_tx,
      unsigned tim
    );
};

#endif
