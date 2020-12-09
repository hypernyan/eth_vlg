`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;
import gateway_sim_pkg::*;

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
    ref logic connected, 
    ref logic listen,
    input int timeout
  );
    int timeout_ctr = 0;
    connect = 1;
    listen = 0;
    forever #(`CLK_PERIOD) begin
      timeout_ctr = timeout_ctr + 1;
      if (connected) begin
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
    ref logic  connect,
    ref logic  connected, 
    ref logic  listen
  );
    connect = 0;
    listen = 1;
  endtask : tcp_listen

endclass : user_logic

module tb (); 

bit clk = 0;
bit rst = 1;
bit send = 0;
initial #100 rst = 0;
always #4 clk <= ~clk;

///////////////////////
// Configure devices //
///////////////////////

localparam [47:0] SERVER_MAC_ADDR  = 48'haadeadbeef01;
localparam [31:0] SERVER_IPV4_ADDR = 32'hc0a80010;
localparam [15:0] SERVER_TCP_PORT  = 1001;
localparam        SERVER_N_TCP     = 1;

localparam [47:0] CLIENT_MAC_ADDR  = 48'hccdeadbeef02;
localparam [31:0] CLIENT_IPV4_ADDR = 32'hc0a80010;
localparam [15:0] CLIENT_TCP_PORT  = 1000;
localparam        CLIENT_N_TCP     = 1;

phy srv_phy_rx  (.*);
phy srv_phy_tx  (.*);
phy cli_phy_rx  (.*);
phy cli_phy_tx  (.*);
phy gate_phy_rx (.*);
phy gate_phy_tx (.*);

byte    cli_tcp_din,        srv_tcp_din;
bit     cli_tcp_vin,        srv_tcp_vin;
bit     cli_tcp_cts,        srv_tcp_cts;
bit     cli_tcp_snd,        srv_tcp_snd;

byte    cli_tcp_dout,       srv_tcp_dout;
bit     cli_tcp_vout,       srv_tcp_vout;

logic   cli_connect,        srv_connect; 
logic   cli_connected,      srv_connected; 
logic   cli_listen,         srv_listen;
ipv4_t  cli_rem_ipv4,       srv_rem_ipv4;
port_t  cli_rem_port,       srv_rem_port;
port_t  cli_loc_port,       srv_loc_port;

logic   cli_ready,          srv_ready;
logic   cli_error,          srv_error;

ipv4_t  cli_preferred_ipv4, srv_preferred_ipv4;
ipv4_t  cli_assigned_ipv4,  srv_assigned_ipv4;
logic   cli_dhcp_success,   srv_dhcp_success;
logic   cli_dhcp_fail,      srv_dhcp_fail;
logic   cli_dhcp_start,     srv_dhcp_start;

parameter int DHCP_TIMEOUT        = 100000;
parameter int TCP_CONNECT_TIMEOUT = 100000;

initial begin
  user_logic   user_cli = new();
  user_logic   user_srv = new();
  srv_connect = 0;
  cli_connect = 0;
  srv_listen = 0;
  cli_listen = 0;
  user_cli.configure(
    cli_preferred_ipv4, cli_loc_port, cli_rem_port, cli_rem_ipv4,
    CLIENT_IPV4_ADDR, CLIENT_TCP_PORT, SERVER_TCP_PORT, SERVER_IPV4_ADDR
  );
  user_srv.configure(
    srv_preferred_ipv4, srv_loc_port, srv_rem_port, srv_rem_ipv4, 
    SERVER_IPV4_ADDR, SERVER_TCP_PORT, CLIENT_TCP_PORT, CLIENT_IPV4_ADDR
  );
  @ (negedge rst)
  fork
    user_cli.dhcp_start(cli_dhcp_start, cli_dhcp_success, cli_dhcp_fail, DHCP_TIMEOUT);
#(`CLK_PERIOD)
    user_srv.dhcp_start(srv_dhcp_start, srv_dhcp_success, srv_dhcp_fail, DHCP_TIMEOUT);
  join
  user_srv.set_ipv4(cli_rem_ipv4, srv_assigned_ipv4);

  user_srv.tcp_listen  (srv_connect, srv_connected, srv_listen);
  user_cli.tcp_connect (cli_connect, cli_connected, cli_listen, TCP_CONNECT_TIMEOUT);
end

/////////////
// Gateway //
/////////////

device_sim #(
  .MAC_ADDRESS  (SERVER_MAC_ADDR),
  .IPV4_ADDRESS (SERVER_IPV4_ADDR)
) device_sim_inst (
  .in     (gate_phy_rx),
  .out    (gate_phy_tx),
  .clk_rx (clk),
  .clk_tx (clk),
  .rst_rx (rst),
  .rst_tx (rst)
);

////////////
// Client //
////////////

eth_vlg #(
  .MAC_ADDR     (CLIENT_MAC_ADDR),
  .ARP_VERBOSE  (0),
  .DHCP_VERBOSE (1),
  .UDP_VERBOSE  (0),
  .IPV4_VERBOSE (0),
  .MAC_VERBOSE  (0)
) cli_inst (
  .clk            (clk),
  .rst            (rst),
  
  .phy_rx         (cli_phy_rx),
  .phy_tx         (cli_phy_tx),

  .tcp_din        (cli_tcp_din),
  .tcp_vin        (cli_tcp_vin),
  .tcp_cts        (cli_tcp_cts),
  .tcp_snd        (cli_tcp_snd),
  
  .tcp_dout       (cli_tcp_dout),
  .tcp_vout       (cli_tcp_vout),
  
  .connect        (cli_connect), 
  .connected      (cli_connected), 
  .listen         (cli_listen),  
  .rem_ipv4       (cli_rem_ipv4),
  .rem_port       (cli_rem_port),
  .loc_port       (cli_loc_port),
  
  // Core status
  .ready          (cli_ready),
  .error          (cli_error),

  .preferred_ipv4 (cli_preferred_ipv4),
  .dhcp_start     (cli_dhcp_start),
  .assigned_ipv4  (cli_assigned_ipv4),
  .dhcp_success   (cli_dhcp_success),
  .dhcp_fail      (cli_dhcp_fail)
);
 
////////////
// Server //
////////////

eth_vlg #(
  .MAC_ADDR     (SERVER_MAC_ADDR),
  .ARP_VERBOSE  (0),
  .DHCP_VERBOSE (1),
  .UDP_VERBOSE  (0),
  .IPV4_VERBOSE (0),
  .MAC_VERBOSE  (0)
) srv_inst (
  .clk            (clk),
  .rst            (rst),

  .phy_rx         (srv_phy_rx),
  .phy_tx         (srv_phy_tx),

  .tcp_din        (srv_tcp_din),
  .tcp_vin        (srv_tcp_vin),
  .tcp_cts        (srv_tcp_cts),
  .tcp_snd        (srv_tcp_snd),

  .tcp_dout       (srv_tcp_dout),
  .tcp_vout       (srv_tcp_vout),

  .connect        (srv_connect), 
  .connected      (srv_connected), 
  .listen         (srv_listen),  
  .rem_ipv4       (srv_rem_ipv4),
  .rem_port       (srv_rem_port),
  .loc_port       (srv_loc_port),
  
  // Core status
  .ready          (srv_ready),
  .error          (srv_error),

  .preferred_ipv4 (srv_preferred_ipv4),
  .dhcp_start     (srv_dhcp_start),
  .assigned_ipv4  (srv_assigned_ipv4),
  .dhcp_success   (srv_dhcp_success),
  .dhcp_fail      (srv_dhcp_fail)
);

/////////////////////
// Ethernet switch //
/////////////////////

parameter SWITCH_PORTS = 3;

logic       switch_vout;
logic [7:0] switch_dout;

assign cli_phy_rx.clk = clk;
assign srv_phy_rx.clk = clk;

assign cli_phy_rx.rst = rst;
assign srv_phy_rx.rst = rst;

// TCP loopback
assign cli_tcp_din = srv_tcp_dout;
assign cli_tcp_vin = srv_tcp_vout;

switch_sim #(
  .N   (3),
  .IFG (10)
) switch_sim_inst (
  .clk  (clk),
  .rst  (rst),

  .din  ({cli_phy_tx.dat, srv_phy_tx.dat, gate_phy_tx.dat}),
  .vin  ({cli_phy_tx.val, srv_phy_tx.val, gate_phy_tx.val}),

  .dout ({cli_phy_rx.dat, srv_phy_rx.dat, gate_phy_rx.dat}),
  .vout ({cli_phy_rx.val, srv_phy_rx.val, gate_phy_rx.val})
);

hexdump  #(
	.FILENAME ("dump/cli"),
	.OFFSET   (1),
	.VERBOSE  (0)
) hexdump_cli_inst (
	.clk (clk),
	.vin (cli_phy_tx.val),
	.din (cli_phy_tx.dat)
);

hexdump  #( 
	.FILENAME ("dump/srv"),
	.OFFSET   (1),
	.VERBOSE  (0)
) hexdump_srv_inst (
	.clk (clk),
	.vin (srv_phy_tx.val),
	.din (srv_phy_tx.dat)
);

endmodule
