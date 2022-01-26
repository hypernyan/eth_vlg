
#ifndef TST_C_H
#define TST_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <iostream>
#include <cstring>
#include <vector>
#include <math.h>
#include <iomanip>
#include "mac_c.h"
#include "ipv4_c.h"
#include <iomanip>
#include<string.h>

class tst_c {

  public :
  
    enum {
      idle_s,
      setup_s,
      reset_s,
      cli_dhcp_dora_s,
      srv_dhcp_dora_s,
      init_dhcp_srv,
      setup_cli_tcp,
      setup_srv_tcp,
      dhcp_check_s,
      done_s
    } state;
    
    // variables for the fsm
    bool cli_dhcp_complete;
    bool srv_dhcp_complete;
    
    void tick (unsigned tim);
    
    unsigned rst_ctr;
    bool rst;

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
    
    tb2dut_t* cli_tb2dut;
    tb2dut_t* srv_tb2dut;
    dut2tb_t* cli_dut2tb;
    dut2tb_t* srv_dut2tb;

    // Parameters of the testcase
    ipv4_c::ipv4_t      cli_ipv4_addr  ;
    ipv4_c::ipv4_t      srv_ipv4_addr  ;
    mac_c::mac_addr_t   cli_mac_addr   ;  
    mac_c::mac_addr_t   srv_mac_addr   ;
    std::string         cli_domain_name;
    std::string         srv_domain_name;
    std::string         cli_hostname   ;
    std::string         srv_hostname   ;
    std::string         cli_fqdn       ;
    std::string         srv_fqdn       ;
    std::string         cli_dut_string ;
    std::string         srv_dut_string ;
    ipv4_c::ipv4_t      default_gateway;
    uint16_t            cli_tcp_port   ;
    uint16_t            srv_tcp_port   ;
    unsigned            mtu            ;

    tst_c (
      ipv4_c::ipv4_t    _cli_ipv4_addr  ,
      ipv4_c::ipv4_t    _srv_ipv4_addr  ,
      mac_c::mac_addr_t _cli_mac_addr   ,
      mac_c::mac_addr_t _srv_mac_addr   ,
      std::string       _cli_domain_name,
      std::string       _srv_domain_name,
      std::string       _cli_hostname   ,
      std::string       _srv_hostname   ,
      std::string       _cli_fqdn       ,
      std::string       _srv_fqdn       ,
      std::string       _cli_dut_string ,
      std::string       _srv_dut_string ,
      ipv4_c::ipv4_t    _default_gateway,
      uint16_t          _cli_tcp_port   ,
      uint16_t          _srv_tcp_port   ,
      unsigned          _mtu
    );
  
    ~tst_c();

};

#endif
