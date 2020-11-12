`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;
import eth_vlg_sim::device_c;

class pkt_parser_c;
  task acquire(
    ref    logic [7:0] d,
    ref    logic       v,
    output byte        pkt[],
    output int         len,
    ref    bit         pkt_v
  );

  enum bit[2:0] {idle_s, acq_s, crc_s} fsm; 
  bit v_prev;
  byte pkt_int [1024];
  int ctr = 0;
  pkt_v = 0;

  forever #(`CLK_PERIOD) begin
    v_prev = v;
    case (fsm)
      idle_s : begin
        if (v) begin
		      $display("starting capture");
		      pkt_int[0] = d;
		      fsm = acq_s;
		    end
	    end
      acq_s : begin
		    ctr = ctr + 1;
		    pkt_int[ctr] = d;
        if (!v) begin
          disable acquire;
		      pkt_v = 1;
		      fsm = idle_s;
          pkt = new[ctr];
          for (int i = 0; i < ctr; i++) pkt[i] = pkt_int[i];
		      $display ("finished capture: len: %d, %p", ctr, pkt);
        end
	    end
      crc_s : begin
        
      end
    endcase
  end
  endtask : acquire
endclass : pkt_parser_c

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

  task automatic connect (
    // dut
    ref logic  _connect,
    ref logic  _connected, 
    ref logic  _listen,
    input int timeout
    );
    int timeout_ctr = 0;
    _connect = 1;
    _listen = 0;
    begin
      forever #(`CLK_PERIOD) begin
      timeout_ctr = timeout_ctr + 1;
      if (_connected) begin
      $display("> Connected."); 
        disable connect;
      end
      if (timeout_ctr == timeout) begin
        $display("> Connection timeout.");
      disable connect;
      end
        end
    end
  endtask : connect

  task automatic listen (
    // dut
    ref logic  _connect,
    ref logic  _connected, 
    ref logic  _listen
  );
     // connections

    //ref logic  connect;
    //ref logic  connected; 
    //ref ipv4_t rem_ipv4;
    //ref port_t rem_port;
    // declarations

    // logic

    _connect = 0;
    _listen = 1;
  endtask : listen

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
localparam        SERVER_N_TCP     = 4;

localparam [47:0] CLIENT_MAC_ADDR  = 48'hccdeadbeef02;
localparam [31:0] CLIENT_IPV4_ADDR = 32'hc0a80011;
localparam [15:0] CLIENT_TCP_PORT  = 1000;
localparam        CLIENT_N_TCP     = 4;

phy srv_phy_rx (.*);
phy srv_phy_tx (.*);
phy cli_phy_rx (.*);
phy cli_phy_tx (.*);
phy gate_phy_rx (.*);
phy gate_phy_tx (.*);

byte cli_tcp_din,           srv_tcp_din;
bit  cli_tcp_vin,           srv_tcp_vin;
bit  cli_tcp_cts,           srv_tcp_cts;
bit  cli_tcp_snd,           srv_tcp_snd;

byte cli_tcp_dout,          srv_tcp_dout;
bit  cli_tcp_vout,          srv_tcp_vout;

logic  cli_connect,         srv_connect; 
logic  cli_connected,       srv_connected; 
logic  cli_listen,          srv_listen;
ipv4_t cli_rem_ipv4,        srv_rem_ipv4;
port_t cli_rem_port,        srv_rem_port;
port_t cli_loc_port,        srv_loc_port;

logic   cli_ready,          srv_ready;
logic   cli_error,          srv_error;

ipv4_t  cli_preferred_ipv4, srv_preferred_ipv4;
ipv4_t  cli_assigned_ipv4,  srv_assigned_ipv4;
logic   cli_dhcp_ipv4_val,  srv_dhcp_ipv4_val;
logic   cli_dhcp_success,   srv_dhcp_success;
logic   cli_dhcp_timeout,   srv_dhcp_timeout;
logic   cli_dhcp_start,     srv_dhcp_start;

initial begin
  user_logic   user_cli = new();
  user_logic   user_srv = new();

  cli_dhcp_start = 0;
  srv_dhcp_start = 0;
  user_srv.configure(
    srv_preferred_ipv4, srv_loc_port, srv_rem_port, srv_rem_ipv4, 
    SERVER_IPV4_ADDR, SERVER_TCP_PORT, CLIENT_TCP_PORT, CLIENT_IPV4_ADDR
  );

  user_cli.configure(
    cli_preferred_ipv4, cli_loc_port, cli_rem_port, cli_rem_ipv4,
    CLIENT_IPV4_ADDR, CLIENT_TCP_PORT, SERVER_TCP_PORT, SERVER_IPV4_ADDR
  );
  @ (negedge rst)
  #8 

  cli_dhcp_start = 1;
  srv_dhcp_start = 1;

  #8 
  cli_dhcp_start = 0;
  srv_dhcp_start = 0;

  user_srv.listen  (srv_connect, srv_connected, srv_listen);
  user_cli.connect (cli_connect, cli_connected, cli_listen, 10000000);

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
  .MAC_ADDR  (CLIENT_MAC_ADDR)
) cli_inst (
  .clk            (clk),
  .rst            (rst),
  .clk_rx         (clk),
  
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
  .dhcp_ipv4_val  (cli_dhcp_ipv4_val),
  .dhcp_success   (cli_dhcp_success),
  .dhcp_timeout   (cli_dhcp_timeout)
);
 
////////////
// Server //
////////////
eth_vlg #(
  .MAC_ADDR  (SERVER_MAC_ADDR)
) srv_inst (
  .clk            (clk),
  .rst            (rst),
  .clk_rx         (clk),

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
  .dhcp_ipv4_val  (srv_dhcp_ipv4_val),
  .dhcp_success   (srv_dhcp_success),
  .dhcp_timeout   (srv_dhcp_timeout)
);

/////////////////////
// Ethernet switch //
/////////////////////
parameter SWITCH_PORTS = 3;

logic       switch_vout;
logic [7:0] switch_dout;

buf_mng #(
  .W (8),
  .N (SWITCH_PORTS),
  .D ({SWITCH_PORTS{12}}),
  .RWW (1)
) buf_mng_inst (
  .clk      (clk),
  .rst      (rst),

  .rst_fifo ({SWITCH_PORTS{rst}}),
  .v_i      ({cli_phy_tx.v, srv_phy_tx.v, gate_phy_tx.v}),
  .d_i      ({cli_phy_tx.d, srv_phy_tx.d, gate_phy_tx.d}),

  .v_o      (switch_vout),
  .d_o      (switch_dout),
  .eof      (),

  .rdy      (1'b1),
  .avl      (),
  .act_ms   ()
);

assign  cli_phy_rx.v = switch_vout;
assign  srv_phy_rx.v = switch_vout;
assign gate_phy_rx.v = switch_vout;

assign  cli_phy_rx.d = switch_dout;
assign  srv_phy_rx.d = switch_dout;
assign gate_phy_rx.d = switch_dout;

// TCP loopback
assign cli_tcp_din = srv_tcp_dout;
assign cli_tcp_vin = srv_tcp_vout;

hexdump  #(
	.FILENAME ("dump_cli"),
	.OFFSET   (1)
) hexdump_cli_inst (
	.clk (clk),
	.vin (cli_phy_tx.v),
	.din (cli_phy_tx.d)
);

hexdump  #( 
	.FILENAME ("dump_srv"),
	.OFFSET   (1)
) hexdump_srv_inst (
	.clk (clk),
	.vin (srv_phy_tx.v),
	.din (srv_phy_tx.d)
);

endmodule
