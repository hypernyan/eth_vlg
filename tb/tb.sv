`include "../sim/util/clkdef.sv"
import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ipv4_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;
import gateway_sim_pkg::*;
import user_logic_pkg::*;
import statistics_pkg::*;

module tb (); 

  logic clk = 0;
  logic rst;
  
  always #(`CLK_PERIOD/2) clk <= ~clk;
  
  rst_gen rst_gen_inst (
    .clk (clk),
    .rst (rst)
  );
  
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
  
  parameter int MTU                  = 1500;
  parameter int DHCP_TIMEOUT         = 100000;
  parameter int TCP_CONNECT_TIMEOUT  = 100000;
  parameter int TCP_TEST_PAYLOAD_LEN = 100000;
  parameter int TCP_RECEIVE_TIMEOUT  = 500000;
  
  phy srv_phy_rx  (.*);
  phy srv_phy_tx  (.*);
  phy cli_phy_rx  (.*);
  phy cli_phy_tx  (.*);
  phy gate_phy_rx (.*);
  phy gate_phy_tx (.*);
  
  logic [7:0] cli_tcp_din,    srv_tcp_din;
  logic       cli_tcp_vin,    srv_tcp_vin;
  logic       cli_tcp_cts,    srv_tcp_cts;
  logic       cli_tcp_snd,    srv_tcp_snd;
  
  logic [7:0] cli_tcp_dout,      srv_tcp_dout;
  logic       cli_tcp_vout,      srv_tcp_vout;
  logic       cli_idle,          srv_idle;
  logic       cli_listening,     srv_listening;
  logic       cli_connecting,    srv_connecting;
  logic       cli_connected,     srv_connected;
  logic       cli_disconnecting, srv_disconnecting;
  logic       cli_connect,       srv_connect; 
  logic       cli_listen,        srv_listen;
  ipv4_t      cli_rem_ipv4,      srv_rem_ipv4;
  port_t      cli_rem_port,      srv_rem_port;
  port_t      cli_loc_port,      srv_loc_port;
  
  logic cli_ready, srv_ready;
  logic cli_error, srv_error;
  
  ipv4_t  cli_preferred_ipv4, srv_preferred_ipv4;
  ipv4_t  cli_assigned_ipv4,  srv_assigned_ipv4;
  logic   cli_dhcp_success,   srv_dhcp_success;
  logic   cli_dhcp_fail,      srv_dhcp_fail;
  logic   cli_dhcp_start,     srv_dhcp_start;
  
  byte data_tx_cli2srv [];
  byte data_tx_srv2cli [];
  byte data_rx_cli2srv [];
  byte data_rx_srv2cli [];
  bit srv_equal, cli_equal;
  bit data_rx_srv2cli_val, data_rx_cli2srv_val;
  logic cli_send, srv_send;
  
  initial begin
    // Create objects
    user_logic_c #(
      .MTU                 (MTU),
      .DHCP_TIMEOUT        (DHCP_TIMEOUT),
      .TCP_CONNECT_TIMEOUT (TCP_CONNECT_TIMEOUT),
      .RANDOM_DATA_LEN     (TCP_TEST_PAYLOAD_LEN),
      .TCP_RECEIVE_TIMEOUT (TCP_RECEIVE_TIMEOUT)
    ) user_cli = new();
  //   
    user_logic_c #(
      .MTU                 (MTU),
      .DHCP_TIMEOUT        (DHCP_TIMEOUT),
      .TCP_CONNECT_TIMEOUT (TCP_CONNECT_TIMEOUT),
      .RANDOM_DATA_LEN     (TCP_TEST_PAYLOAD_LEN),
      .TCP_RECEIVE_TIMEOUT (TCP_RECEIVE_TIMEOUT)
    ) user_srv = new();
  // 
    //stat_c     stat     = new();
    // Set initial control and data signals
    srv_connect    = 0;
    cli_connect    = 0;
    srv_listen     = 0;
    cli_listen     = 0;
    cli_tcp_snd    = 0;
    srv_tcp_snd    = 0;
    cli_dhcp_start = 0;
    srv_dhcp_start = 0;
    srv_send = 0;
    cli_send = 0;
    // Set local and remote IPs and ports
    $display("=== Configuring client and server... ===");
    user_cli.configure (
      cli_preferred_ipv4, cli_loc_port, cli_rem_port, cli_rem_ipv4,
      CLIENT_IPV4_ADDR, CLIENT_TCP_PORT, SERVER_TCP_PORT, SERVER_IPV4_ADDR
    );
    user_srv.configure (
      srv_preferred_ipv4, srv_loc_port, srv_rem_port, srv_rem_ipv4, 
      SERVER_IPV4_ADDR, SERVER_TCP_PORT, CLIENT_TCP_PORT, CLIENT_IPV4_ADDR
    );
    // Initialize DHCP request for DUTs
    @ (negedge rst)
    #(`CLK_PERIOD)
    $display("=== Initializing DHCP... ===");
    fork
      user_cli.dhcp_start (cli_dhcp_start, cli_dhcp_success, cli_dhcp_fail, DHCP_TIMEOUT);
      #(`CLK_PERIOD) // Wait 1 tick so server generates an different DHCP xid
      user_srv.dhcp_start (srv_dhcp_start, srv_dhcp_success, srv_dhcp_fail, DHCP_TIMEOUT);
    join
    //if (cli_dhcp_success) $display("=== Client DHCP assigned IP %d.%d.%d.%d ===", );
    //else if (cli_dhcp_fail) $display("=== Client DHCP failed to obtain IP.");
  
    // Set client's remote ip to connect to (as assigned to server by DHCP)
    user_srv.set_ipv4 (cli_rem_ipv4, srv_assigned_ipv4); // todo: change object to cli
    // Transition server into listen state
    user_srv.tcp_listen (srv_connect, srv_connected, srv_listen);
    // Client will attempt to connect
    user_cli.tcp_connect (cli_connect, cli_connected, srv_connected, cli_listen, TCP_CONNECT_TIMEOUT);
    // Generate random data in both directions
    user_cli.gen_data (TCP_TEST_PAYLOAD_LEN, data_tx_cli2srv);
    user_srv.gen_data (TCP_TEST_PAYLOAD_LEN, data_tx_srv2cli);
    #1000
    // Send and receive generated data
    srv_send = 1;
    cli_send = 1;
    #(`CLK_PERIOD) 
    srv_send = 0;
    cli_send = 0;
    @ (posedge (data_rx_srv2cli_val && data_rx_cli2srv_val))
    fork
      user_cli.comp (data_tx_cli2srv, data_rx_cli2srv, cli_equal);
      user_srv.comp (data_tx_srv2cli, data_rx_srv2cli, srv_equal);
    join
    if (srv_equal && cli_equal) $display("Server and client received correct payload. Test passed");
    else $display("Server or client received incorrect payload. Test failed");
    $finish();
  end
  
  ///////////////////////////////
  // Raw TCP sender simulators //
  ///////////////////////////////
  
  sender sender_cli_inst (
    .clk  (clk),
    .rst  (rst),
    .dout (cli_tcp_din),
    .vout (cli_tcp_vin),
    .cts  (cli_tcp_cts),
    .data (data_tx_srv2cli),
    .val  (cli_send)
  );
  
  sender sender_srv_inst (
    .clk  (clk),
    .rst  (rst),
    .dout (srv_tcp_din),
    .vout (srv_tcp_vin),
    .cts  (srv_tcp_cts),
    .data (data_tx_cli2srv),
    .val  (srv_send)
  );
  
  /////////////////////////////////
  // Raw TCP receiver simulators //
  /////////////////////////////////

  receiver #(
    .TIMEOUT (TCP_RECEIVE_TIMEOUT)
  ) receiver_cli_inst (
    .clk  (clk),
    .rst  (rst),
    .din  (cli_tcp_dout),
    .vin  (cli_tcp_vout),
    .data (data_rx_cli2srv),
    .val  (data_rx_cli2srv_val)
  );
  
  receiver #(
    .TIMEOUT (TCP_RECEIVE_TIMEOUT)
  ) receiver_srv_inst (
    .clk  (clk),
    .rst  (rst),
    .din  (srv_tcp_dout),
    .vin  (srv_tcp_vout),
    .data (data_rx_srv2cli),
    .val  (data_rx_srv2cli_val)
  );
  
  /////////////////
  //// Gateway ////
  // DHCP server //
  /////////////////
  
  device_sim #(
    .MAC_ADDRESS  (SERVER_MAC_ADDR)
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
    .MAC_ADDR        (CLIENT_MAC_ADDR),               // Device MAC
    .DEFAULT_GATEWAY ({8'd192, 8'd168, 8'd0, 8'hd1}), // Default gateway IP address
    .MTU             (MTU),                          // Maximum Transmission Unit
         
    .TCP_RETRANSMIT_TICKS      (1250),  // TCP will try to rentransmit a packet after approx. TCP_RETRANSMIT_TICKS*(2**TCP_PACKET_DEPTH)
    .TCP_SACK_RETRANSMIT_TICKS (125),   
    .TCP_RETRANSMIT_TRIES      (10),        // Number of retransmission tries before aborting connection
    .TCP_RX_RAM_DEPTH          (13),       // RAM depth of transmission buff. Amount of bytes may be stored unacked 
    .TCP_TX_RAM_DEPTH          (13),       // RAM depth of transmission buff. Amount of bytes may be stored unacked 
    .TCP_PACKET_DEPTH          (4),        // RAM depth of packet information. Amout of generated packets may be stored
    .TCP_WAIT_TICKS            (125),      // Wait before forming a packet with current data. May be overriden by tcp_snd
    .TCP_CONNECTION_TIMEOUT    (125000000), 
    .TCP_ACK_TIMEOUT           (2500),    
    .TCP_FORCE_ACK_PACKETS     (5),
    .TCP_KEEPALIVE_PERIOD      (600000000), 
    .TCP_KEEPALIVE_INTERVAL    (12500000),  
    .TCP_ENABLE_KEEPALIVE      (1),
    .TCP_KEEPALIVE_TRIES       (5),
  
    .DOMAIN_NAME_LEN    (5),
    .HOSTNAME_LEN       (6),
    .FQDN_LEN           (8),
    .DOMAIN_NAME        ("fpga0"),    // Domain name
    .HOSTNAME           ("host_0"),   // Hostname
    .FQDN               ("host_fq0"), // Fully Qualified Domain Name
    .DHCP_TIMEOUT       (12500),  // DHCP server reply timeout
    .DHCP_ENABLE        (1),          // Synthesyze DHCP (Ignored, always 1)
  
    .ARP_TABLE_SIZE     (8),
  
    .MAC_CDC_FIFO_DEPTH (8),
    .MAC_CDC_DELAY      (3),
  
    .ICMP_VERBOSE       (0),
    .TCP_VERBOSE        (1),
    .ARP_VERBOSE        (0),
    .DHCP_VERBOSE       (0),
    .UDP_VERBOSE        (0),
    .IPV4_VERBOSE       (0),
    .MAC_VERBOSE        (0),
    .DUT_STRING         ("cli")
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
    .listen         (cli_listen),
  
    .rem_ipv4       (cli_rem_ipv4),
    .rem_port       (cli_rem_port),
    .loc_port       (cli_loc_port),
    
    .idle           (cli_idle),
    .listening      (cli_listening),
    .connecting     (cli_connecting),
    .connected      (cli_connected),
    .disconnecting  (cli_disconnecting),
  
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
    .MAC_ADDR        (SERVER_MAC_ADDR), // Device MAC
    .DEFAULT_GATEWAY ({8'd192, 8'd168, 8'd0, 8'hd1}),         // Default gateway IP address
    .MTU             (MTU),                                  // Maximum Transmission Unit
         
    .TCP_RETRANSMIT_TICKS      (1250),  // TCP will try to rentransmit a packet after approx. TCP_RETRANSMIT_TICKS*(2**TCP_PACKET_DEPTH)
    .TCP_SACK_RETRANSMIT_TICKS (125),   
    .TCP_RETRANSMIT_TRIES      (10),    // Number of retransmission tries before aborting connection
    .TCP_RX_RAM_DEPTH          (13),    // RAM depth of transmission buff. Amount of bytes may be stored unacked 
    .TCP_TX_RAM_DEPTH          (13),    // RAM depth of transmission buff. Amount of bytes may be stored unacked 
    .TCP_PACKET_DEPTH          (4),     // RAM depth of packet information. Amout of generated packets may be stored
    .TCP_WAIT_TICKS            (125),   // Wait before forming a packet with current data. May be overriden by tcp_snd
    .TCP_CONNECTION_TIMEOUT    (125000000), 
    .TCP_ACK_TIMEOUT           (2500),    
    .TCP_FORCE_ACK_PACKETS     (5),
    .TCP_KEEPALIVE_PERIOD      (600000000), 
    .TCP_KEEPALIVE_INTERVAL    (12500000),  
    .TCP_ENABLE_KEEPALIVE      (1),
    .TCP_KEEPALIVE_TRIES       (5),
  
    .DOMAIN_NAME_LEN    (5),       
    .HOSTNAME_LEN       (6),
    .FQDN_LEN           (8),
    .DOMAIN_NAME        ("fpga1"),     // Domain name
    .HOSTNAME           ("host_1"),    // Hostname
    .FQDN               ("host_fq1"),  // Fully Qualified Domain Name
    .DHCP_TIMEOUT       (12500),     // DHCP server reply timeout
    .DHCP_ENABLE        (1),           // Synthesyze DHCP (Ignored, always 1)
  
    .MAC_CDC_FIFO_DEPTH (8), // GMII/RGMII phy_rx.clk->clk is synchronized with RAM
    .MAC_CDC_DELAY      (3), // Introduce a delay to avoid packed discontinuities if phy's clk is a bit slower
  
    .ARP_TABLE_SIZE     (8), // ARP table RAM depth
  
    .ICMP_VERBOSE       (0),
    .TCP_VERBOSE        (1),
    .ARP_VERBOSE        (1),
    .DHCP_VERBOSE       (0),
    .UDP_VERBOSE        (0),
    .IPV4_VERBOSE       (0),
    .MAC_VERBOSE        (0),
    .DUT_STRING         ("srv")
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
    .listen         (srv_listen),
  
    .rem_ipv4       (srv_rem_ipv4),
    .rem_port       (srv_rem_port),
    .loc_port       (srv_loc_port),
  
    .idle           (srv_idle),
    .listening      (srv_listening),
    .connecting     (srv_connecting),
    .connected      (srv_connected),
    .disconnecting  (srv_disconnecting),
  
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
  
  switch_sim #(
    .N          (3),
    .IFG        (10),
    .LOSS_RATE  (0.0)
    //.ERROR_RATE (0.05)
  ) switch_sim_inst (
    .clk  (clk),
    .rst  (rst),
    .connected (cli_connected && srv_connected),
    .din  ({cli_phy_tx.dat, srv_phy_tx.dat, gate_phy_tx.dat}),
    .vin  ({cli_phy_tx.val, srv_phy_tx.val, gate_phy_tx.val}),
  
    .dout ({cli_phy_rx.dat, srv_phy_rx.dat, gate_phy_rx.dat}),
    .vout ({cli_phy_rx.val, srv_phy_rx.val, gate_phy_rx.val})
  );
  
endmodule
