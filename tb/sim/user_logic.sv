`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ipv4_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;

class user_logic;
 
  task automatic set_port (
    ref port_t port,
    input port_t _port
  );
    port = _port;
  endtask : set_port

  task automatic set_ipv4 (
    ref ipv4_t ipv4,
    input ipv4_t _ipv4
  );
    ipv4 = _ipv4;
  endtask : set_ipv4

  task automatic configure (
    ref ipv4_t preferred_ipv4,
    ref port_t loc_port,
    ref port_t rem_port,
    ref ipv4_t rem_ipv4,

    input ipv4_t _preferred_ipv4,
    input port_t _loc_port,
    input port_t _rem_port,
    input ipv4_t _rem_ipv4
  ); 
    set_ipv4(preferred_ipv4, _preferred_ipv4);
    set_port(rem_port, _rem_port);
    set_port(loc_port, _loc_port);
    set_ipv4(rem_ipv4, _rem_ipv4);
  endtask : configure
  
  task automatic dhcp_start (
    ref logic start,
    ref logic success,
    ref logic fail,
    input int timeout
  );
    int timeout_ctr = 0;
    start = 1;
    #(`CLK_PERIOD)
    start = 0;
    while (!(success || fail || (timeout_ctr == timeout))) begin
      #(`CLK_PERIOD)
      timeout_ctr = timeout_ctr + 1;
      if (success) begin
        $display("> DHCP success."); 
      end
      if (fail) begin
        $display("> DHCP fail."); 
      end
      if (timeout_ctr == timeout) begin
        $display("> DHCP timeout.");
      end
    end
  endtask : dhcp_start

  task automatic tcp_connect (
    // dut
    ref logic connect,
    ref logic connected_cli, 
    ref logic connected_srv, 
    ref logic listen,
    input int timeout
  );
    int timeout_ctr = 0;
    connect = 1;
    listen = 0;
    forever #(`CLK_PERIOD) begin
      timeout_ctr = timeout_ctr + 1;
      if (connected_cli && connected_srv) begin
        $display("> Connected."); 
        disable tcp_connect;
      end
      if (timeout_ctr == timeout) begin
        $display("> Connection timeout.");
      disable tcp_connect;
      end
    end
  endtask : tcp_connect

  task automatic tcp_listen (
    ref logic connect,
    ref logic connected, 
    ref logic listen
  );
    connect = 0;
    listen = 1;
  endtask : tcp_listen

  task automatic gen_data (
    input int len,
    output byte data []
  );
    data = new[len];
    for (int i = 0; i < len; i++) data[i] = $random();
  endtask : gen_data

  task automatic send (
    input byte        data [],
    ref   logic [7:0] dat,
    ref   logic       val,
    ref   logic       cts
  );
    int ctr = 0;
   // while (ctr < data.size()) begin
   //   if (cts) begin
   //     #(`CLK_PERIOD) 
   //     ctr = ctr + 1;
   //     val = 1;
   //     dat = data[ctr];
   //   end
   //   else begin
   //     #(`CLK_PERIOD) 
   //     val = 0;
   //   end
   // end
   // val = 0;
  endtask : send

  task automatic receive (
    output byte       data [],
    ref   logic [7:0] dat,
    ref   logic       val,
    input int         timeout
  );
  int ctr_to = 0;
  int ctr = 0;
    while (ctr_to < timeout) begin
      #(`CLK_PERIOD)
      if (val) begin
        data[ctr] = dat;
        ctr = ctr + 1;
      end
      else ctr_to = ctr_to + 1;
    end
  endtask : receive

endclass : user_logic
