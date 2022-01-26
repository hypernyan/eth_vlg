#ifndef DEV_C_H
#define DEV_C_H

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <queue>
#include <fstream>
#include <string.h>

#include "../hdr/dhcp_c.h"
#include "../hdr/arp_c.h"
#include "../hdr/icmp_c.h"
#include "../hdr/pcap.h"

class dev_c {

  public:
    typedef enum {
      none,
      proto_arp,
      proto_icmp,
      proto_udp,
      proto_tcp,
      proto_dhcp
    } proto_t;

    static const size_t IFG_TICKS  = 20;
    
    ipv4_c::ipv4_t IPV4_BROADCAST;
    
    dev_c (
      const ipv4_c::ipv4_t    _ipv4_addr,
      const ipv4_c::ipv4_t    _subnet_mask,
      const mac_c::mac_addr_t _mac_addr,
      const bool              _mac_verbose,
      const bool              _ipv4_verbose,
      const bool              _arp_verbose,
      const bool              _icmp_verbose,
      const bool              _udp_verbose,
      const bool              _dhcp_verbose
    );

    ~dev_c ();
    
    // device parameters
    ipv4_c::ipv4_t    ip_addr;
    ipv4_c::ipv4_t    subnet_mask;
    mac_c::mac_addr_t mac_addr;
    bool              ipv4_verbose;
    bool              arp_verbose;
    bool              icmp_verbose;
    bool              udp_verbose;
    bool              dhcp_verbose;

    unsigned cur_tim;
    unsigned tx_ptr;
    unsigned ifg_ctr;
    unsigned rx_idx;
    size_t   len_tx;

    // protocol handlers
    dhcp_c* dhcp;
    arp_c*  arp;
    icmp_c* icmp;
    // pcap log
    pcap*   pcap_log;

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
    bool process_tx (char& dat, bool& val);

    void tx_add_pkt (std::vector<uint8_t>& pkt);

    uint32_t ipv4_to_uint32 (const ipv4_c::ipv4_t& ipv4);

    void process (
      char     dat_rx,
      bool     val_rx,
      char&    dat_tx,
      bool&    val_tx,
      unsigned tim
    );

};

#endif
