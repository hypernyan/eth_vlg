`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;

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
  byte pkt [1024];
  int ctr = 0;
  pkt_v = 0;
  forever #(`CLK_PERIOD) begin
    v_prev = v;
    case (fsm)
      idle_s : begin
        if (v) begin
		  $display("starting capture");
		  pkt[0] = d;
		  fsm = acq_s;
		end
	  end
      acq_s : begin
		ctr = ctr + 1;
		pkt[ctr] = d;
        if (!v) begin
		  pkt_v = 1;
		  fsm = idle_s;
		  $display ("finished capture: len: %d, %p", ctr, pkt);
        end
	  end
      crc_s : begin
        
      end
    endcase
  end
  endtask : acquire

//  task parse_arp()
//  task parse_()

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

logic clk = 0;
logic rst = 1;
logic send = 0;
initial #100 rst = 0;
always #4 clk <= ~clk;

///////////////////////
// Configure devices //
///////////////////////

localparam [47:0] SERVER_MAC_ADDR  = 48'hdeadbeef01;
localparam [31:0] SERVER_IPV4_ADDR = 32'hc0a80101;
localparam [15:0] SERVER_TCP_PORT  = 1001;
localparam        SERVER_N_TCP     = 4;

localparam [47:0] CLIENT_MAC_ADDR  = 48'hdeadbeef02;
localparam [31:0] CLIENT_IPV4_ADDR = 32'hc0a80115;
localparam [15:0] CLIENT_TCP_PORT  = 1000;
localparam        CLIENT_N_TCP     = 4;

phy phy (.*);
phy phy_cli2srv (.*);
phy phy_srv2cli (.*);

fsm_t cli_fsm, srv_fsm;

logic [7:0] tcp_cli_din, tcp_srv_din;
logic tcp_cli_vin, tcp_srv_vin;

logic [7:0] cli_dout;
logic cli_vout;
logic [7:0] srv_dout;
logic srv_vout;

logic  connect_cli, connect_srv; 
logic  connected_cli, connected_srv; 
logic  listen_cli, listen_srv;
ipv4_t rem_ipv4_cli, rem_ipv4_srv;
port_t rem_port_cli, rem_port_srv, loc_port_cli, loc_port_srv;

logic tcp_cli_cts, tcp_srv_cts;

logic [$clog2(12500)-1:0] cli_ctr, srv_ctr;
logic [10:0] cli_tx_ctr, srv_tx_ctr;

logic [7:0] phy_cli2srv_d;
logic       phy_cli2srv_v;

logic [7:0] phy_srv2cli_d;
logic       phy_srv2cli_v;


assign phy_cli2srv_d = phy_cli2srv.d;
assign phy_cli2srv_v = phy_cli2srv.v;

assign phy_srv2cli_d = phy_srv2cli.d;
assign phy_srv2cli_v = phy_srv2cli.v;

initial begin
  user_logic user_cli = new();
  user_logic user_srv = new();
  pkt_parser_c parser = new();
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
  parser.acquire(phy_cli2srv_d, phy_cli2srv_v );
end

typedef struct {
  real loss; // ~ %of packets completely lost
  real corrupt;
 } phy_param_t;

/*
ethernet_phy ethernet_cli_to_srv (
  .clk        (),
  .phy_params (),
  .in_v       (),
  .in_d       (),
  .out_v      (),
  .out_d      ()
);

ethernet_phy ethernet_srv_to_cli (
  .clk        (),
  .phy_params (),
  .in_v       (phy_tx_srv.v),
  .in_d       (phy_tx_srv.d),
  .out_v      (phy_rx_cli.v),
  .out_d      (phy_rx_cli.d)
);
*/
// Client logic

udp udp_tx_cli(.*);
udp udp_rx_cli(.*);

eth_vlg #(
  .IPV4_ADDR (CLIENT_IPV4_ADDR),
  .MAC_ADDR  (CLIENT_MAC_ADDR)
) cli_inst (
  .clk       (clk),
  .rst       (rst),
  .phy_rx    (phy_srv2cli),
  .phy_tx    (phy_cli2srv),
  
  .udp_tx    (udp_tx_cli),
  .udp_rx    (udp_rx_cli),
  
  .tcp_din   (tcp_din_cli),
  .tcp_vin   (tcp_vin_cli),
  .tcp_cts   (tcp_cts_cli),
  
  .tcp_dout  (dout_cli),
  .tcp_vout  (vout_cli),
  
  .connect   (connect_cli), 
  .connected (connected_cli), 
  .listen    (listen_cli),  
  .rem_ipv4  (rem_ipv4_cli),
  .rem_port  (rem_port_cli),
  .loc_port  (loc_port_cli)

);

udp udp_tx_srv(.*);
udp udp_rx_srv(.*);

eth_vlg #(
  .IPV4_ADDR (SERVER_IPV4_ADDR),
  .MAC_ADDR  (SERVER_MAC_ADDR)
) srv_inst (
  .clk       (clk),
  .rst       (rst),
  .phy_rx    (phy_cli2srv),
  .phy_tx    (phy_srv2cli),
  
  .udp_tx    (udp_tx_srv),
  .udp_rx    (udp_rx_srv),
   
  .tcp_din   (tcp_din_srv),
  .tcp_vin   (tcp_vin_srv),
  .tcp_cts   (tcp_cts_srv),
  
  .tcp_dout  (dout_srv),
  .tcp_vout  (vout_srv),
  
  .connect   (connect_srv), 
  .connected (connected_srv), 
  .listen    (listen_srv),  
  .rem_ipv4  (rem_ipv4_srv),
  .rem_port  (rem_port_srv),
  .loc_port  (loc_port_srv)

);

endmodule
