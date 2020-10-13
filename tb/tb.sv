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
  //file_t file;
  task automatic test (  
  input int payload_length,
  input real packet_loss,
  input int tx_buffer_size,
  input int rx_buffer_size
  );

  $display("Starting TCP test...");
  $display("Interface speed: 1 Gbit.");
  $display("MTU: 1460 bytes.");
  $display("Server transmit buffer size: %d bytes", 2**tx_buffer_size);
  $display("Server receive buffer size: %d bytes",  2**rx_buffer_size);
  $display("Client transmit buffer size: %d bytes", 2**tx_buffer_size);
  $display("Client receive buffer size: %d bytes",  2**rx_buffer_size);
  $display("====================================");
  $display("Target transmission speed: 500Mbps");
  $display("Server to client payload length: %d bytes", payload_length);
  //connect(
  //  connect_cli, 
  //  connected_cli, 
  //  listen_cli,  
  //  rem_ipv4_cli,
  //  rem_port_cli);
  //transfer_file();
  endtask : test

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
    // local ports
    ref port_t loc_port,
    // target ports
    ref port_t rem_port,
      // target ipv4s
    ref ipv4_t rem_ipv4,
      
    // local ports
    input port_t _loc_port,
    // target ports
    input port_t _rem_port,
      // target ipv4s
    input ipv4_t _rem_ipv4
  ); 
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
localparam [31:0] SERVER_IPV4_ADDR = 32'hc0a80101;
localparam [15:0] SERVER_TCP_PORT  = 1001;
localparam        SERVER_N_TCP     = 4;

localparam [47:0] CLIENT_MAC_ADDR  = 48'hccdeadbeef02;
localparam [31:0] CLIENT_IPV4_ADDR = 32'hc0a80115;
localparam [15:0] CLIENT_TCP_PORT  = 1000;
localparam        CLIENT_N_TCP     = 4;

phy phy (.*);
phy phy_cli2srv (.*);
phy phy_srv2cli (.*);

udp udp_tx_cli(.*);
udp udp_rx_cli(.*);

udp udp_tx_srv(.*);
udp udp_rx_srv(.*);

byte tcp_din_cli, tcp_din_srv;
bit  tcp_vin_cli, tcp_vin_srv;
bit  tcp_cts_cli, tcp_cts_srv;
bit  tcp_snd_cli, tcp_snd_srv;

byte tcp_dout_cli, tcp_dout_srv;
bit  tcp_vout_cli, tcp_vout_srv;

logic  connect_cli, connect_srv; 
logic  connected_cli, connected_srv; 
logic  listen_cli, listen_srv;
ipv4_t rem_ipv4_cli, rem_ipv4_srv;
port_t rem_port_cli, rem_port_srv, loc_port_cli, loc_port_srv;

initial begin
  user_logic   user_cli = new();
  user_logic   user_srv = new();
 // pkt_parser_c parser   = new();
 // device_c     device   = new();
  user_srv.configure(
    loc_port_srv, rem_port_srv, rem_ipv4_srv, 
    SERVER_TCP_PORT, CLIENT_TCP_PORT, CLIENT_IPV4_ADDR
  );
  user_cli.configure(
    loc_port_cli, rem_port_cli, rem_ipv4_cli, 
    CLIENT_TCP_PORT, SERVER_TCP_PORT, SERVER_IPV4_ADDR
  );
  user_srv.listen (connect_srv, connected_srv, listen_srv);
  user_cli.connect (connect_cli, connected_cli, listen_cli, 10000000);
  @(posedge tcp_cts_srv) begin
    #8
    $display("Client CTS detected. Transmitting 1 byte of data");
    tcp_din_cli = 8'hdf;
    tcp_vin_cli = 1;
  end
  #8
    tcp_vin_cli = 0;
    @(posedge tcp_vout_srv) $display("Response detected");
end

// Client logic
/*
device_sim #(
  .MAC_ADDRESS (SERVER_MAC_ADDR),
  .IPV4_ADDRESS (SERVER_IPV4_ADDR)
) device_sim_inst (
  .in  (phy_cli2srv),
  .out (phy_srv2cli),
  .clk_rx (clk),
  .clk_tx (clk),
  .rst_rx (rst),
  .rst_tx (rst)
);
*/

logic [$clog2(125000000)-1:0] ctr = 0;
logic dhcp_ipv4_req;

always @ (posedge clk) begin
  dhcp_ipv4_req <= (ctr == 125000000);
  ctr <= (ctr == 125000000) ? 0 : ctr + 1;
end

eth_vlg #(
  .IPV4_ADDR (CLIENT_IPV4_ADDR),
  .MAC_ADDR  (CLIENT_MAC_ADDR)
) cli_inst (
  .clk       (clk),
  .rst       (rst),
  .clk_rx    (clk),
  
  .phy_rx    (phy_srv2cli),
  .phy_tx    (phy_cli2srv),
  
  .udp_tx    (udp_tx_cli),
  .udp_rx    (udp_rx_cli),
  
  .tcp_din   (tcp_din_cli),
  .tcp_vin   (tcp_vin_cli),
  .tcp_cts   (tcp_cts_cli),
  .tcp_snd   (tcp_snd_cli),
  
  .tcp_dout  (tcp_dout_cli),
  .tcp_vout  (tcp_vout_cli),
  
  .connect   (connect_cli), 
  .connected (connected_cli), 
  .listen    (listen_cli),  
  .rem_ipv4  (rem_ipv4_cli),
  .rem_port  (rem_port_cli),
  .loc_port  (loc_port_cli),
  
  .dhcp_ipv4_req     (dhcp_ipv4_req),
  .dhcp_pref_ipv4    (CLIENT_IPV4_ADDR),
  .dhcp_ipv4_addr    (dhcp_ipv4_addr),
  .dhcp_ipv4_val     (dhcp_ipv4_val),
  .dhcp_ok      (dhcp_ok),
  .dhcp_timeout (dhcp_timeout)
);

eth_vlg #(
  .IPV4_ADDR (SERVER_IPV4_ADDR),
  .MAC_ADDR  (SERVER_MAC_ADDR)
) srv_inst (
  .clk       (clk),
  .rst       (rst),
  .clk_rx    (clk),

  .phy_rx    (phy_cli2srv),
  .phy_tx    (phy_srv2cli),
  
  .udp_tx    (udp_tx_srv),
  .udp_rx    (udp_rx_srv),
   
  .tcp_din   (tcp_din_srv),
  .tcp_vin   (tcp_vin_srv),
  .tcp_cts   (tcp_cts_srv),
  .tcp_snd   (tcp_snd_srv),

  .tcp_dout  (tcp_dout_srv),
  .tcp_vout  (tcp_vout_srv),
  
  .connect   (connect_srv), 
  .connected (connected_srv), 
  .listen    (listen_srv),  
  .rem_ipv4  (rem_ipv4_srv),
  .rem_port  (rem_port_srv),
  .loc_port  (loc_port_srv)

);

assign tcp_din_srv = tcp_dout_srv;
assign tcp_vin_srv = tcp_vout_srv;


hexdump  #( 
	.FILENAME ("dump_cli"), 
	.OFFSET   (4) 
) hexdump_cli_inst (
	.clk (clk), 
	.vin (phy_cli2srv.v), 
	.din (phy_cli2srv.d) 
);

hexdump  #( 
	.FILENAME ("dump_srv"), 
	.OFFSET   (4) 
) hexdump_srv_inst (
	.clk (clk), 
	.vin (phy_srv2cli.v), 
	.din (phy_srv2cli.d) 
);

endmodule
