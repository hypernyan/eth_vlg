////////////////////////////////////////////////////////////////////////////////
//
// Filename:   eth_vlg.cpp
//
// Project:  Verilog Tutorial Example file
//
// Purpose:  This is an example Verilator test bench driver file eth_vlg
//    module.
//
//  Heads up: I may have left a bug or two in this design for you to fix.
//
// Creator:  Dan Gisselquist, Ph.D.
//    Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Written and distributed by Gisselquist Technology, LLC
//
// This program is hereby granted to the public domain.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <arpa/inet.h>
#include <linux/if_packet.h>
#include <stdio.h>
#include <cstring>
#include <string>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <net/if.h>
#include <netinet/ether.h>

class adapter_c {
  public :
    static const size_t RXBUF_SIZE = 65536;
    static const size_t TXBUF_SIZE = 65536;
    static const size_t IFG_TICKS  = 20;
    static const uint32_t CRC_POLY = 0xEDB88320;
    uint32_t crc;

  adapter_c (
    size_t RXBUF_SIZE,
    size_t TXBUF_SIZE,
    char ifcname [16]
  );

  ~adapter_c();
  char ifName[16];

  int fcs_ctr;
  struct ifreq if_idx;
  struct ifreq if_mac;
  uint32_t crc_tbl[256];

struct sockaddr_ll socket_address;

  bool open ();
  ssize_t snd (size_t len);
  ssize_t rcv (void* buf[], size_t len);
  bool tx_proc (char& dat, bool& val,  char* buf, ssize_t& len);
  void rx_proc (char& dat, bool& val);
  void proc (char& dat_rx, bool& val_rx, char dat_tx, bool val_tx);
  void gen_crc_table (uint32_t (&tbl) [256]);

  uint32_t fcs (char& b);
  unsigned ctr = 0;
    char* buf_tx;
    //char* txbuf;
    char rxbuf [RXBUF_SIZE];
    char txbuf [TXBUF_SIZE];


  private :

    typedef enum {
      idle_s,
      pre_s,
      pld_s,
      fcs_s
    } pkt_s;
    
    pkt_s rx_s;
    pkt_s tx_s;
    
    int sock;
    int len_rx;
    int tx_idx;
    int rx_idx;
    int ifg_ctr;
    int pre_tx_ctr;
    int pre_rx_ctr;

};
