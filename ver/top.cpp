#include <stdio.h>
#include <stdlib.h>
#include "Vtop.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "../hdr/dev_c.h"
#include "../hdr/usr.h"
#include <arpa/inet.h>
#include <linux/if_packet.h>
#include <stdio.h>
#include <string.h>
#include <iostream>
#include <thread>
#include <atomic>
#include <pthread.h>
#include "adapter.h"

const int SIMTIME = 1<<10;
const int N = 2;
const bool IPV4_VERBOSE = true;
const ipv4_c::ipv4_t    IP_ADDR = {192, 168, 1, 1};
const ipv4_c::ipv4_t    SUBNET_MASK = {255, 255, 255, 0};
const mac_c::mac_addr_t MAC_ADDR = {0xde, 0xad, 0xfa, 0xce, 0xed, 0xff};

unsigned tim = 0;

VerilatedVcdC* tfp;
Vtop *tb;
dev_c *dev;
usr *user;

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

void mainloop (){
  VerilatedVcdC* tfp = new VerilatedVcdC;
  tb->trace(tfp, 99);
  tfp->open("eth_vlg.vcd");
  tb->preferred_ipv4[1] = 0xc0a8010f;
  tb->preferred_ipv4[0] = 0xc0a80110;
  tb->rst = 1;
  tick(++tim, tb, tfp);
  tb->rst = 0;
  tick(++tim, tb, tfp);
  tb->dhcp_start[0]  = 1;
  tick(++tim, tb, tfp);
  tb->dhcp_start[1]  = 1;
  
  tb->tcp_listen[0]  = 0;
  tb->tcp_listen[1]  = 1;
  
  tb->tcp_connect[0] = 1;
  tb->tcp_connect[1] = 0;
  
  tb->tcp_loc_port[0] = 1000;
  tb->tcp_loc_port[1] = 2000;
  
  tb->tcp_rem_port[0] = 2000;
  tb->tcp_rem_port[1] = 1000;
  tb->tcp_rem_ipv4[0] = 0xc0a8010f;

  tick(++tim, tb, tfp);
  tb->dhcp_start[0] = 0;
  tb->dhcp_start[1] = 0;
  
  while (!key_pressed) {
    char rxdat = 0;
    bool rxval = 0;
    tick(++tim, tb, tfp);
    //tb->rst = user->rst(tim);
    for (int i = 0; i < N; i++) {
      user->tb2dut[i].tcp_din         = tb->tcp_din         [i];
      user->tb2dut[i].tcp_vin         = tb->tcp_vin         [i];
      user->tb2dut[i].tcp_snd         = tb->tcp_snd         [i];
      user->tb2dut[i].tcp_rem_ipv4    = tb->tcp_rem_ipv4    [i];
      user->tb2dut[i].tcp_rem_port    = tb->tcp_rem_port    [i];
      user->tb2dut[i].tcp_loc_port    = tb->tcp_loc_port    [i];
      user->tb2dut[i].tcp_connect     = tb->tcp_connect     [i];
      user->tb2dut[i].tcp_listen      = tb->tcp_listen      [i];
      user->tb2dut[i].udp_len         = tb->udp_len         [i];
      user->tb2dut[i].udp_din         = tb->udp_din         [i];
      user->tb2dut[i].udp_vin         = tb->udp_vin         [i];
      user->tb2dut[i].udp_loc_port    = tb->udp_loc_port    [i];
      user->tb2dut[i].udp_ipv4_tx     = tb->udp_ipv4_tx     [i];
      user->tb2dut[i].udp_rem_port_tx = tb->udp_rem_port_tx [i];
      user->tb2dut[i].preferred_ipv4  = tb->preferred_ipv4  [i];
      //user->tb2dut.dhcp_start      = tb->dhcp_start      ; 
     // tb->tcp_cts        [i] = user->dut2tb[i].tcp_cts        ;
     // tb->tcp_dout       [i] = user->dut2tb[i].tcp_dout       ;
     // tb->tcp_vout       [i] = user->dut2tb[i].tcp_vout       ;
     // tb->tcp_con_ipv4   [i] = user->dut2tb[i].tcp_con_ipv4   ;
     // tb->tcp_con_port   [i] = user->dut2tb[i].tcp_con_port   ;
     // tb->udp_cts        [i] = user->dut2tb[i].udp_cts        ;
     // tb->udp_dout       [i] = user->dut2tb[i].udp_dout       ;
     // tb->udp_vout       [i] = user->dut2tb[i].udp_vout       ;
     // tb->udp_ipv4_rx    [i] = user->dut2tb[i].udp_ipv4_rx    ;
     // tb->udp_rem_port_rx[i] = user->dut2tb[i].udp_rem_port_rx;
     // tb->idle           [i] = user->dut2tb[i].idle           ;
     // tb->listening      [i] = user->dut2tb[i].listening      ;
     // tb->connecting     [i] = user->dut2tb[i].connecting     ;
     // tb->connected      [i] = user->dut2tb[i].connected      ;
     // tb->disconnecting  [i] = user->dut2tb[i].disconnecting  ;
     // tb->ready          [i] = user->dut2tb[i].ready          ;
     // tb->error          [i] = user->dut2tb[i].error          ;
     // tb->assigned_ipv4  [i] = user->dut2tb[i].assigned_ipv4  ;
     // tb->dhcp_lease     [i] = user->dut2tb[i].dhcp_lease     ;
    }
    if (tb->connected[0] && tb->connected[1]) {
      tb->tcp_din[0] = (tb->tcp_cts[0]) ? tb->tcp_din[0] + 1 : tb->tcp_din[0];
      tb->tcp_vin[0] = tb->tcp_cts[0];
      tb->tcp_din[1] = (tb->tcp_cts[1]) ? tb->tcp_din[1] + 1 : tb->tcp_din[1];
      tb->tcp_vin[1] = tb->tcp_cts[1];
    }
    dev->process(tb->phy_tx_dat, tb->phy_tx_val, rxdat, rxval, tim);
    tb->phy_rx_val = rxval;
    tb->phy_rx_dat = rxdat;
  }
}

int main(int argc, char **argv) {
  //acp_cli usr;
  dev = new dev_c (IP_ADDR, SUBNET_MASK, MAC_ADDR, IPV4_VERBOSE);
  user = new usr;
  Verilated::commandArgs(argc, argv);
  tb = new Vtop;
  Verilated::traceEverOn(true);
  std::thread loop_thread = thread(mainloop);
  system("read -n1");
  key_pressed = true;
  loop_thread.join();
  dev->~dev_c();
  user->~usr();
  return 0;
}
