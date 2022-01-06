//            ____________________________________________________________
//           |  _______     _______        _______              _______  |
//           | |eth_vlg|   |       |      |  esg  |            |       | |    _______ 
//           | |  TCP <-----> esg <-exec->|  to   |<-commands->|  rhd  | |   |RHD2000|
//           | |       |   |  ___  |      |  rhd  |--settings->|  SPI <-SPI->|   IC  |
//    _____  | |       |   | |RAM|<------>|_______|            |_______| |   |_______|                      
//   | PHY | | |       |   | |___| |                                     |    
//   | IC <-----> PHY  |   |       |                                     |      
//   |_____| | |_______|   |_______|                                     |
//           |___________________________________________________________|

module top (
	// Ethernet Cyclone 10 LP development kit
	input logic       rgmii_rx_clk,
	input logic       rgmii_rx_ctl,
  input logic [3:0] rgmii_rx_dat,

	output logic       rgmii_gtx_clk,
	output logic       rgmii_tx_ctl, 
  output logic [3:0] rgmii_tx_dat, 

	output logic mdc,
	output logic mdio,

	input logic reset_n,
  // Ethernet connections
  output logic [3:0] led,
  input  logic       gen_clk_125m,
  input  logic       gen_clk_100m,
  input  logic       gen_clk_50m
);

  parameter [3:0][7:0] PREFERRED_IPV4 = {8'd192, 8'd168, 8'd1, 8'd213};
  parameter [1:0][7:0] TCP_LOCAL_PORT = 1000;
  
  parameter int UDP_SEND_PERIOD = 1250000;
  parameter int UDP_PAYLOAD_SIZE = 1000;

  localparam int REFCLK_HZ = 125000000;

  logic arst;
  assign arst = !reset_n;
  
  logic [7:0] phy_rx_dat;
  logic       phy_rx_val;
  logic       phy_rx_err;
  logic       phy_rx_clk;
  
  logic [7:0] phy_tx_dat;
  logic       phy_tx_val;
  logic       phy_tx_err;
  logic       phy_tx_clk;
  
  logic [7:0] gmii_rx_dat, gmii_tx_dat;
  logic       gmii_rx_val, gmii_tx_val;
  logic       gmii_rx_err, gmii_tx_err;
  
  logic clk_125m;

  assign clk_125m = gen_clk_125m;

  logic  [15:0] udp_len;
  port_t        udp_loc_port;   
  ipv4_t        udp_ipv4_rx;    
  port_t        udp_rem_port_rx;
  ipv4_t        udp_ipv4_tx;    
  port_t        udp_rem_port_tx;
  ipv4_t        con_ipv4;
  port_t        con_port;
  logic [7:0]   tcp_din;
  logic         tcp_vin;
  logic         tcp_cts;
  logic         tcp_snd;
  logic [7:0]   tcp_dout;
  logic         tcp_vout;
  ipv4_t        rem_ipv4;
  port_t        rem_port;
  logic         connect;
  port_t        loc_port;
  logic         listen;
  logic         connected;
  
  logic   ready;
  logic   error;
  
  ipv4_t  preferred_ipv4;
  ipv4_t  assigned_ipv4;
  logic   dhcp_lease;
  logic   dhcp_timeout;

  logic [$clog2(UDP_SEND_PERIOD)-1:0] ctr;
  logic [11:0] ctr_tx;
  logic [7:0] udp_din;
  logic       udp_vin;
  logic tcp_vout_prev;
  logic [23:0] phase_inc;
  logic [13:0] i;
  logic [7:0] ram_a_dl;

  // Configure local ip and port
  assign preferred_ipv4 = PREFERRED_IPV4;
  assign loc_port       = TCP_LOCAL_PORT;
  
  assign led[0] = ~connected && ready;
  
  // Configure UDP 
  assign udp_loc_port    = 1000;
  assign udp_ipv4_tx     = con_ipv4; 
  assign udp_rem_port_tx = 1234;

  // Maximum possible throughput
  always @ (posedge clk_125m) begin
    if (tcp_cts) begin
      tcp_vin <= 1'b1;
      tcp_din <= tcp_din + 1;
    end
    else tcp_vin <= 0;
  end

  ///////////////////
  // RGMII DDR I/O //
  ///////////////////
  
  rgmii_adapter #(
    .VENDOR       ("INTEL"),
    .FAMILY       ("CYCLONE 10 LP"),
    .USE_RX_PLL   ("TRUE"),
    .USE_TX_PLL   ("TRUE")
  ) rgmii_adapter_inst (
    .arst          (arst),          // in

    .rgmii_rx_clk  (rgmii_rx_clk),  // in
    .rgmii_rx_dat  (rgmii_rx_dat),  // in
    .rgmii_rx_ctl  (rgmii_rx_ctl),  // in

    .rgmii_gtx_clk (rgmii_gtx_clk), // out
    .rgmii_tx_dat  (rgmii_tx_dat),  // out
    .rgmii_tx_ctl  (rgmii_tx_ctl),  // out

    .gmii_rx_clk   (phy_rx_clk), // out
    .gmii_rx_rst   (), // out
    .gmii_rx_dat   (phy_rx_dat), // out
    .gmii_rx_val   (phy_rx_val), // out
    .gmii_rx_err   (phy_rx_err), // out

    .gmii_clk_125m (clk_125m),
    .gmii_tx_dat   (phy_tx_dat), // in
    .gmii_tx_val   (phy_tx_val), // in
    .gmii_tx_err   (phy_tx_err),  // in
    .gmii_tx_rst   (rst)         // out
  );

  ///////////
  // Stack //
  ///////////

  eth_vlg #(
    .MAC_ADDR        ({8'h0C,8'hAB,8'hFA,8'hCE,8'hBE,8'hEF}),// MAC ADDRESS
    .DEFAULT_GATEWAY ({8'd192, 8'd168, 8'd1, 8'hd1}),
    .MTU             (1500),

    .TCP_RETRANSMIT_TICKS      (250000),
    .TCP_SACK_RETRANSMIT_TICKS (20000),
    .TCP_RETRANSMIT_TRIES      (5),
    .TCP_RX_RAM_DEPTH          (13),
    .TCP_TX_RAM_DEPTH          (13),
    .TCP_PACKET_DEPTH          (5),
    .TCP_WAIT_TICKS            (1000),
    .TCP_CONNECTION_TIMEOUT    (REFCLK_HZ),
    .TCP_ACK_TIMEOUT           (125000),
    .TCP_KEEPALIVE_PERIOD      (600000000),
    .TCP_KEEPALIVE_INTERVAL    (60000),
    .TCP_ENABLE_KEEPALIVE      (1),
    .TCP_KEEPALIVE_TRIES       (5),

    .DOMAIN_NAME_LEN (5),
    .HOSTNAME_LEN    (8),
    .FQDN_LEN        (9),
    .DOMAIN_NAME     ("fpga0"),
    .HOSTNAME        ("fpga_eth"),
    .FQDN            ("fpga_host"),
    .DHCP_TIMEOUT_SEC (3),
    .DHCP_ENABLE     (1),
    .ARP_VERBOSE     (0),
    .DHCP_VERBOSE    (0),
    .UDP_VERBOSE     (0),
    .IPV4_VERBOSE    (0)
  ) eth_vlg_inst (
    .clk            (clk_125m),   // Internal 125 MHz
    .rst            (rst),        // Reset synchronous to clk
    
//    .phy_rx (phy_rx),
//    .phy_tx (phy_tx),
    .phy_rx_clk     (phy_rx_clk),
    .phy_rx_err     (phy_rx_err),
    .phy_rx_val     (phy_rx_val),
    .phy_rx_dat     (phy_rx_dat),

    .phy_tx_clk     (phy_tx_clk),
    .phy_tx_err     (phy_tx_err),
    .phy_tx_val     (phy_tx_val),
    .phy_tx_dat     (phy_tx_dat),

    .udp_len        (udp_len),
    .udp_din        (udp_din),
    .udp_vin        (udp_vin),
    .udp_cts        (udp_cts),
    .udp_dout       (udp_dout),
    .udp_vout       (udp_vout),

    .udp_loc_port    (udp_loc_port),
    .udp_ipv4_rx     (udp_ipv4_rx),
    .udp_rem_port_rx (udp_rem_port_rx),
    .udp_ipv4_tx     (udp_ipv4_tx),
    .udp_rem_port_tx (udp_rem_port_tx),

    // Raw TCP
    .tcp_din         (tcp_din),
    .tcp_vin         (tcp_vin),
    .tcp_cts         (tcp_cts),
    .tcp_snd         (tcp_snd),

    .tcp_dout        (tcp_dout),
    .tcp_vout        (tcp_vout),

    .tcp_rem_ipv4    (rem_ipv4),
    .tcp_loc_port    (loc_port),
    .tcp_rem_port    (rem_port),
    .tcp_con_ipv4    (con_ipv4),
    .tcp_con_port    (con_port),
    .tcp_connect     (connect),
    .connected       (connected),
    .tcp_listen      (listen),
    // Core status
    .ready           (ready),
    .error           (error),
    // DHCP related
    .preferred_ipv4  (preferred_ipv4),
    .assigned_ipv4   (assigned_ipv4),
    .dhcp_start      (dhcp_start),
    .dhcp_lease      (dhcp_lease)
  );
  
  logic ready_prev;
  logic [15:0] rst_prev;

  // attempt to aqcure DHCP lease every second
  logic [$clog2(REFCLK_HZ)-1:0] dhcp_start_ctr;
  always @ (posedge clk_125m) begin
    dhcp_start_ctr <= (dhcp_start_ctr == REFCLK_HZ) ? 0 : dhcp_start_ctr + 1;
  end

  always @ (posedge clk_125m) begin
    rst_prev[15:0] <= {rst_prev[14:0], rst};
    listen     <= dhcp_lease;
    dhcp_start <= (dhcp_start_ctr == 0) && !dhcp_lease;
  end

/*
  acp_ext_if ext (.*); // parameter values
  exe_if     exe (.*); // commands to execute
  evt_if     evt (.*);  

  acp acp_inst (
    .clk  (clk_125m),
    .rst  (!connected),

    .rxd  (tcp_dout),
    .rxv  (tcp_vout),

    .txd  (tcp_din),
    .txv  (tcp_vin),
    .txen (),
    .cts  (tcp_cts),

    .ext  (ext),
    .exe  (exe),
    .evt  (evt)
  );
*/
endmodule
