#include <stdio.h>
#include <stdlib.h>
#include "Vtop.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "../hdr/dev_c.h"
#include "../hdr/tst_c.h"
#include <stdio.h>
#include <string.h>
#include <iostream>
#include <thread>
#include <atomic>
#include <pthread.h>

#define COLOR_RED     "\x1b[31m"
#define COLOR_GREEN   "\x1b[32m"
#define COLOR_YELLOW  "\x1b[33m"
#define COLOR_BLUE    "\x1b[34m"
#define COLOR_MAGENTA "\x1b[35m"
#define COLOR_CYAN    "\x1b[36m"
#define COLOR_RESET   "\x1b[0m"

const int SIMTIME = 1<<20;
const int N = 2;

// Common parameters
const int DHCP_TIMEOUT = 100000;
const int ARP_TIMEOUT  = 10000;
const int ICMP_TIMEOUT = 10000;
const int DNS_TIMEOUT  = 10000;
const int TCP_CONNECT_TIMEOUT = 100000;
unsigned MTU = 1500;

// Simulated device configuration
const ipv4_c::ipv4_t    SUBNET_MASK = {255, 255, 255, 0};
const ipv4_c::ipv4_t    IP_ADDR = {192, 168, 1, 123};
const ipv4_c::ipv4_t    PRIMARY_DNS = {192, 168, 1, 123};
const ipv4_c::ipv4_t    SECONDARY_DNS = {192, 168, 1, 123};
const ipv4_c::ipv4_t    DEFAULT_GATEWAY = {255, 255, 255, 0};
const mac_c::mac_addr_t MAC_ADDR = {0xde, 0xad, 0xfa, 0xce, 0xed, 0xff};
const bool IPV4_VERBOSE = false;
const bool ARP_VERBOSE  = true;
const bool MAC_VERBOSE  = false;
const bool ICMP_VERBOSE = true;
const bool UDP_VERBOSE  = false;
const bool DHCP_VERBOSE = true;

// DUT configuration
const ipv4_c::ipv4_t     CLIENT_IPV4_ADDR = {192, 168, 1, 200};
const ipv4_c::mac_addr_t CLIENT_MAC_ADDR  = {0xde, 0xad, 0xbe, 0xef, 0x00, 0x01};
const uint16_t           CLIENT_TCP_PORT  = 1000;

const ipv4_c::ipv4_t     SERVER_IPV4_ADDR = {192, 168, 1, 100};
const ipv4_c::mac_addr_t SERVER_MAC_ADDR  = {0xde, 0xad, 0xbe, 0xef, 0x00, 0x02};
const uint16_t           SERVER_TCP_PORT  = 1000;

// Testbench state machine
enum {
  idle_s,      // Test start
  setup_s,     // Setup DUTs
  reset_s,     // Release DUT resets

  dhcp_dora_s, // Initialize DORA
  dhcp_wait_s, // Wait for DHCP to complete for both DUT
  dhcp_test_dora_s,
  dhcp_test_renew_s,
  dhcp_test_rebind_s,
  dhcp_result_s,
  
  dns_request_s,
  dns_test_s,
  
  arp_request_s, // Generate single ARP requests
  arp_test_s,   // Wait for ARP replies
  arp_reply_s,   // Wait for ARP replies
  arp_result_s,  // Compare ARP results
  
  icmp_request_s, // Generate single ICMP requests (ping)
  icmp_test_s,   // Wait for Ping replies
  icmp_result_s,  // Compare ARP results
  tcp_test_s,
  tcp_connect_s,
  done_s
} state;
    

unsigned tim = 0;
unsigned rst_ctr = 0;
unsigned dhcp_timeout = 0;
unsigned arp_timeout  = 0;
unsigned dns_timeout  = 0;
unsigned icmp_timeout = 0;
unsigned tcp_connect_timeout = 0;
char rxdat = 0;
bool rxval = 0;

bool dhcp_fail[N];
bool arp_fail[N];
bool icmp_fail[N];

bool test_complete;

VerilatedVcdC* tfp;
Vtop *tb;
dev_c *dev;
tst_c *tst;

atomic_bool key_pressed(false);

void tick(int tim, Vtop *tb, VerilatedVcdC* tfp) {
  tb->eval();
  if (tfp) tfp->dump(tim*2-1);
  tb->clk = 1;
  tb->phy_rx_clk = 1;
  tb->eval();
  if (tfp) tfp->dump(tim*2);
  tb->clk = 0;
  tb->phy_rx_clk = 0;
  tb->eval();
  if (tfp) {
    tfp->dump(tim*2+1);
    tfp->flush();
  }
}

int main(int argc, char **argv) {
  dev = new dev_c (
    IP_ADDR,
    SUBNET_MASK,
    MAC_ADDR,
    MAC_VERBOSE,
    IPV4_VERBOSE,
    ARP_VERBOSE,
    ICMP_VERBOSE,
    UDP_VERBOSE,
    DHCP_VERBOSE
  );
  Verilated::commandArgs(argc, argv);
  tb = new Vtop;
  Verilated::traceEverOn(true);
  VerilatedVcdC* tfp = new VerilatedVcdC;
  tb->trace(tfp, 99);
  tfp->open("eth_vlg.vcd");
  tb->rst = 1;
  test_complete = 0;
  
  while (!test_complete) {
    dev->process(tb->phy_tx_dat, tb->phy_tx_val, rxdat, rxval, tim);
    tb->phy_rx_val = rxval;
    tb->phy_rx_dat = rxdat;
    tick(++tim, tb, tfp);
    switch (state) {
      case (idle_s) : {
        printf("=== eth_vlg testbench ===\n");
        tb->rst = 0;
        state = setup_s;
        break;
      }
      case (setup_s) : {
        // DHCP
        tb->preferred_ipv4[0] = dev->ipv4_to_uint32(CLIENT_IPV4_ADDR);
        tb->preferred_ipv4[1] = dev->ipv4_to_uint32(SERVER_IPV4_ADDR);
        // TCP
        tb->tcp_rem_ipv4[0] = dev->ipv4_to_uint32(SERVER_IPV4_ADDR);
        tb->tcp_rem_port[0] = SERVER_TCP_PORT;  
        tb->tcp_loc_port[0] = CLIENT_TCP_PORT;

        tb->tcp_rem_ipv4[1] = {0};
        tb->tcp_rem_port[1] = 0;
        tb->tcp_loc_port[1] = SERVER_TCP_PORT;

        dhcp_timeout = 0;
        arp_timeout = 0;

        state = reset_s;
        break;
      }
      case (reset_s) : {
        rst_ctr++;
        if (rst_ctr == 10) tb->rst = 0;
        if (rst_ctr == 20) state = dhcp_dora_s;
        break;
      }
      case (dhcp_dora_s) : {
        tb->dhcp_start[0] = 1;
        // delay by 1 tick to avout same prng number for xid
        if (tb->dhcp_start[0]) 
          tb->dhcp_start[1] = 1;
        state = dhcp_wait_s;
        break;
      }
      case (dhcp_wait_s) : {
        tb->dhcp_start[0] = 0;
        tb->dhcp_start[1] = 0;
        state = dhcp_test_dora_s;
        printf(COLOR_BLUE "DHCP test starting..." COLOR_RESET "\n");
        break;
      }
      case (dhcp_test_dora_s) : {
        if (dhcp_timeout++ == DHCP_TIMEOUT) {
          if (dev->dhcp->check_lease(CLIENT_IPV4_ADDR, CLIENT_MAC_ADDR) &&
          tb->dhcp_lease[0] &&
          dev->dhcp->check_lease(SERVER_IPV4_ADDR, SERVER_MAC_ADDR) &&
          tb->dhcp_lease[1]) {
            printf(COLOR_GREEN "DHCP PASS" COLOR_RESET "\n");
          } else {
            printf(COLOR_RED "DHCP FAIL" COLOR_RESET "\n");
          }
          state = dns_request_s;
        }
        break;
      }
      case (dns_request_s) : {
        printf(COLOR_BLUE "DNS test starting..." COLOR_RESET "\n");
        tb->dns_ipv4_pri[0] = dev->ipv4_to_uint32(PRIMARY_DNS);
        tb->dns_ipv4_sec[0] = dev->ipv4_to_uint32(SECONDARY_DNS);
        tb->dns_start[0]    = true;
        state = dns_test_s;
        break;
      }
      case (dns_test_s) : {
        tb->dns_start[0] = false;
        if (dns_timeout++ == DNS_TIMEOUT) {
          state = arp_request_s;
          break;
        }
      }
      case (arp_request_s) : {
        printf(COLOR_BLUE "ARP test starting..." COLOR_RESET "\n");
        dev->arp->create_entry(CLIENT_IPV4_ADDR);
        dev->arp->create_entry(SERVER_IPV4_ADDR);
        state = arp_test_s;
        break;
      }
      case (arp_test_s) : {
        if (arp_timeout++ == ARP_TIMEOUT) {
          if (dev->arp->check(CLIENT_MAC_ADDR, CLIENT_IPV4_ADDR) &&
            dev->arp->check(SERVER_MAC_ADDR, SERVER_IPV4_ADDR)) {
            printf(COLOR_GREEN "ARP PASS" COLOR_RESET "\n");
          } else {
            arp_fail[0] = 1;
            printf(COLOR_RED "ARP FAIL" COLOR_RESET "\n");
          }
          state = icmp_request_s;
        }
        break;
      }
      case (icmp_request_s) : {
        printf("ICMP test starting...\n");
        dev->icmp->ping_add(CLIENT_IPV4_ADDR, CLIENT_MAC_ADDR);
        dev->icmp->ping_add(SERVER_IPV4_ADDR, SERVER_MAC_ADDR);
        state = icmp_test_s;
        break;
      }
      case (icmp_test_s) : {
        if (icmp_timeout++ == ICMP_TIMEOUT) {
          if (dev->icmp->check() == 0) {
            printf(COLOR_GREEN "ICMP PASS" COLOR_RESET "\n");
          } else {
            arp_fail[0] = 1;
            printf(COLOR_RED "ICMP FAIL" COLOR_RESET "tcp_connect_s\n");
          }
          state = tcp_test_s;
        }
        break;
      }
      case (tcp_test_s) : {
        printf("TCP connection test starting...\n");
        state = tcp_connect_s;
        tb->tcp_connect[0] = 1;
        tb->tcp_listen[0]  = 0;
        tb->tcp_connect[1] = 0;
        tb->tcp_listen[1]  = 1;
        break;
      }
      case (tcp_connect_s) : {
        if (tcp_connect_timeout++ == TCP_CONNECT_TIMEOUT) {
          if (tb->connected[0] && tb->connected[1]) {
            printf(COLOR_GREEN "TCP connected..." COLOR_RESET "\n");
          } else {
            //arp_fail[0] = 1;
            printf(COLOR_RED "TCP failed to connect..." COLOR_RESET "\n");
          }
          state = done_s;
        }
        break;
      }
      case (done_s) : {
        test_complete = true;
        break;
      }
    }
  }

  dev->~dev_c();
  return 0;
}
