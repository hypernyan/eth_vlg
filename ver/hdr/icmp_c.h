#ifndef ICMP_C_H
#define ICMP_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>
#include "../hdr/ipv4_c.h"
#include "../hdr/mac_c.h"

class icmp_c : virtual public ipv4_c{

  public : 
    icmp_c (
      const ipv4_c::ipv4_t    _ipv4_addr,
      const mac_c::mac_addr_t _mac_addr,
      const bool              _verbose,
      const bool              _ipv4_verbose,
      const bool              _mac_verbose
    );
    ~icmp_c();
    // maximum number of ICMP request packets
    // sent, but not received a reply yet 
    ipv4_c::ipv4_t dev_ipv4;
    mac_c::mac_addr_t dev_mac;
    uint16_t icmp_seq; // current sequence for requests
    bool verbose;

    unsigned error_count;
    unsigned success_count;
    
    static constexpr uint8_t  QUEUE_SIZE    = 8;
    static constexpr unsigned TIMEOUT_TICKS = 10000;

    static constexpr uint8_t ICMP_ECHO_REPLY   = 0;
    static constexpr uint8_t ICMP_ECHO_REQUEST = 8;

    struct icmp_hdr_t {
      uint8_t  icmp_type;
      uint8_t  icmp_code;
      uint32_t icmp_cks;
      uint32_t icmp_id;
      uint32_t icmp_seq;
    };

    struct icmp_entry_t {
      bool       sent; // request sent
      bool       done; // request sent
      bool       success; // request sent
      unsigned   timer;  // timeout timer
      ipv4_t     ipv4;   // 
      mac_addr_t mac;   // 
      uint16_t   seq;    // 
    };
    
    std::vector <icmp_entry_t> entry;

    struct icmp_meta_t {
      icmp_hdr_t         icmp_hdr;
      ipv4_c::ipv4_hdr_t ipv4_hdr;
      mac_c::mac_hdr_t   mac_hdr;
    };

    unsigned check ();
    
    bool ping_add (
      ipv4_c::ipv4_t ipv4,
      mac_c::mac_addr_t mac
    );

    bool icmp_parse    (
      std::vector<uint8_t>& pkt, 
      icmp_meta_t& meta
    );

    void icmp_generate (
      std::vector<uint8_t>& pkt,
      icmp_meta_t& meta
    );

    // process icmp
    void icmp_process (
    std::vector<uint8_t>  pkt_rx,
    bool                  val_rx,
    std::vector<uint8_t>& pkt_tx,
    bool&                 val_tx
    );

    bool ping_request (
      ipv4_c::ipv4_t& ipv4
    );

    void request_process (
      bool                &val_rx,
      icmp_c::icmp_meta_t &meta_rx,
      bool                &val_tx,
      icmp_c::icmp_meta_t &meta_tx
    );
};

#endif