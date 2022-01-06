#ifndef USR_C_H
#define USR_C_H

#include <stdio.h>
#include <stdlib.h>
#include "Vtop.h"
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>

class usr {

  public :

    static const int MAC_ADDR_BITS  = 48;
    static const int IPV4_ADDR_BITS = 32;
    static const int PORT_ADDR_BITS = 16;
    static const int DATAPATH_BITS  = 8;
    static const int N              = 2;

    struct tb2dut_t {
      uint8_t  tcp_din         ;
      bool     tcp_vin         ;
      bool     tcp_snd         ;
      uint32_t tcp_rem_ipv4    ;                             
      uint16_t tcp_rem_port    ;                             
      uint16_t tcp_loc_port    ;
      bool     tcp_connect     ;                              
      bool     tcp_listen      ;  
      uint16_t udp_len         ;      
      uint8_t  udp_din         ;      
      bool     udp_vin         ;
      uint16_t udp_loc_port    ;  
      uint32_t udp_ipv4_tx     ;   
      uint16_t udp_rem_port_tx ;
      uint32_t preferred_ipv4  ;
      bool     dhcp_start      ; 
    };

    struct dut2tb_t {
      bool     tcp_cts         ;
      uint8_t  tcp_dout        ;
      bool     tcp_vout        ;    
      uint32_t tcp_con_ipv4    ;                          
      uint16_t tcp_con_port    ;
      bool     udp_cts         ;      
      uint8_t  udp_dout        ;
      bool     udp_vout        ;
      uint32_t udp_ipv4_rx     ;   
      uint16_t udp_rem_port_rx ;
      bool     idle            ;         
      bool     listening       ;    
      bool     connecting      ;   
      bool     connected       ;    
      bool     disconnecting   ;
      bool     ready           ;
      bool     error           ;
      uint32_t assigned_ipv4   ; 
      bool     dhcp_lease      ;  
    };

    tb2dut_t tb2dut [N];
    dut2tb_t dut2tb [N];
    
    usr ();
    ~usr ();

    long tb2rtls(uint64_t val, int b);
    unsigned long tb2rtlus(uint64_t val, int b);
   // void clear(std::vector<uint8_t> &q)

    void configure (
      uint16_t udp_loc_port,
      uint32_t udp_ipv4_tx,
      uint16_t udp_rem_port_tx,
      bool     tcp_connect,
      bool     tcp_listen,
      uint32_t tcp_rem_ipv4,
      uint32_t tcp_rem_port,
      uint16_t tcp_loc_port,
      uint32_t preferred_ipv4
    );


    void pcap_create (std::string name);
    void pcap_write_pkt_hdr (); 


    void receive(int time, uint8_t dat, bool val); //ifc_t upd (ifc_t ifc);
    bool rst (int tim);
    void snd();
    void rcv(int time);

  private:
    std::vector<std::string> q;
    static const int RST_HIGH_TICKS = 10;
    static const int RX_TIMEOUT_TICKS = 100;
    int len;
    int tx_ctr;
    int rx_timeout;
    std::string str_rx;

};

#endif