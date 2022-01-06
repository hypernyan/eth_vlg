#ifndef PCAP_C_H
#define PCAP_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <iostream>
#include <cstring>
#include <vector>
#include <math.h>
#include <iomanip>
//  The ACP client class methods are divied into 
// 1. public -> physical receive/transmit lines with DUT
// 2. private -> methods to process FSM, gather errors, etc.

using namespace std;

class pcap {

  public :
    pcap(std::string name, int ns_per_tick);
    ~pcap();
    void write_pkt (int ticks, std::vector<uint8_t>);
    ofstream f;
    
  private:
    uint32_t MAGIC_NUMBER  = 0xa1b2c3d4;
    uint16_t VERSION_MAJOR = 0x0002; 
    uint16_t VERSION_MINOR = 0x0004;
    uint32_t THISZONE      = 0x00000000;
    uint32_t SIGFIGS       = 0x00000000;
    uint32_t SNAPLEN       = 0x00040000;
    uint32_t NETWORK       = 0x00000001;
    
    int tick_len;

    bool open_file (std::string name);
    void close_file ();
    void write_pkt_hdr (int ticks, size_t len);
    void write_global_hdr ();
};

#endif
