#ifndef ARP_C_H
#define ARP_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>
#include "../hdr/mac_c.h"
#include "../hdr/ipv4_c.h"

class arp_c : virtual public mac_c {

  public :
    static const unsigned ARP_ENTRY_LIFE    = 100000;
    static const unsigned TRANSMIT_INTERVAL = 10000;
    static const unsigned REQUEST_RETRIES   = 10;

    
    struct arp_hdr_t {
      uint16_t   htype;
      uint16_t   ptype;
      uint8_t    hlen;
      uint8_t    plen;
      uint16_t   opcode;
      mac_addr_t     sha;
      ipv4_c::ipv4_t spa;
      mac_addr_t     tha;
      ipv4_c::ipv4_t tpa;
    };

    struct entry_t {
      mac_addr_t     mac;
      ipv4_c::ipv4_t ipv4;
      bool           bound;
      unsigned       tries;          // failed ARP requests
      unsigned       timer;          // entry considered valid
      unsigned       transmit_timer; // arp retransmissions
    };

    std::vector <entry_t> entry;

    bool verbose;

    arp_c  (
      mac_c::mac_addr_t _mac,
      ipv4_c::ipv4_t    _ipv4,
      bool              _verbose,
      bool              _mac_verbose
    );
    
    ~arp_c ();

    // Parse an Ethernet packet for ARP. Return true if packet is ARP
    bool arp_parse (
      std::vector<uint8_t>& pkt,
      arp_hdr_t& hdr
    );

    // Process internal ARP logic. Receives and generates packets
    // 'pkt_rx/tx' rx/tx packet byte vector
    // 'val_rx/tx' rx/tx packet valid at this tick
    // 1-tick val pulse per packet
    void arp_process (    
      std::vector<uint8_t>  pkt_rx,
      bool                  val_rx,
      std::vector<uint8_t>& pkt_tx,
      bool&                 val_tx
    );

    bool check (
      mac_c::mac_addr_t mac,
      ipv4_c::ipv4_t ipv4
    );

    bool find_mac (
      mac_addr_t& mac,
      unsigned& idx
    );

    bool find_ipv4 (
      ipv4_c::ipv4_t& ipv4,
      unsigned& idx
    );
        
    void create_entry (
      ipv4_c::ipv4_t ipv4
    );

    void clear_table ();

  private :

    void arp_request (
      std::vector<uint8_t>& pkt,
      ipv4_c::ipv4_t ipv4
    );

    // 
    void arp_reply (
      std::vector<uint8_t>& pkt,
      ipv4_c::ipv4_t ipv4,
      mac_c::mac_addr_t mac
    );

    mac_c::mac_addr_t dev_mac;
    ipv4_c::ipv4_t    dev_ipv4;

    void arp_generate (
      std::vector<uint8_t>& pkt,
      arp_hdr_t& hdr
    );

    void process_entry (
      mac_c::mac_addr_t mac,
      ipv4_c::ipv4_t ipv4
    );

};

#endif