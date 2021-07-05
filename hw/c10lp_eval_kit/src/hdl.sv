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
  
  logic arst;
  assign arst = !reset_n;
  
  phy phy_rx(.*);
  phy phy_tx(.*);
  
  logic [7:0] gmii_rx_dat, gmii_tx_dat;
  logic       gmii_rx_val, gmii_tx_val;
  logic       gmii_rx_err, gmii_tx_err;
  
  logic clk_125m;
  assign clk_125m = gen_clk_125m;
  
  logic [7:0] tcp_din;
  logic       tcp_vin;
  logic       tcp_cts;
  logic       tcp_snd;
  logic [7:0] tcp_dout;
  logic       tcp_vout;
  ipv4_t      rem_ipv4;
  port_t      rem_port;
  logic       connect;
  port_t      loc_port;
  logic       listen;
  logic       connected;
  
  logic   ready;
  logic   error;
  
  ipv4_t  preferred_ipv4;
  ipv4_t  assigned_ipv4;
  logic   dhcp_success;
  logic   dhcp_timeout;
  
  assign preferred_ipv4 = PREFERRED_IPV4;
  assign loc_port       = TCP_LOCAL_PORT;
  
  assign led[0] = ~connected && ready;
  
  ////////////////
  // Speed test //
  ////////////////
  
   always @ (posedge clk_125m) begin
     if (tcp_cts) begin
       tcp_vin <= tcp_vout;
       tcp_din <= tcp_dout;
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
  
    .gmii_rx_clk   (phy_rx.clk), // out
    .gmii_rx_rst   (phy_rx.rst), // out
    .gmii_rx_dat   (phy_rx.dat), // out
    .gmii_rx_val   (phy_rx.val), // out
    .gmii_rx_err   (phy_rx.err), // out
  
    .gmii_clk_125m (clk_125m),
    .gmii_tx_dat   (phy_tx.dat), // in
    .gmii_tx_val   (phy_tx.val), // in
    .gmii_tx_err   (phy_tx.err),  // in
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
    .TCP_CONNECTION_TIMEOUT    (125000000), 
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
    .DHCP_TIMEOUT    (375000000),
    .DHCP_ENABLE     (1),
    .ARP_VERBOSE     (0),
    .DHCP_VERBOSE    (0),
    .UDP_VERBOSE     (0),
    .IPV4_VERBOSE    (0)
  ) eth_vlg_inst (
    .clk            (clk_125m),   // Internal 125 MHz
    .rst            (rst),        // Reset synchronous to clk
  
    .phy_rx         (phy_rx),
    .phy_tx         (phy_tx),
  
    // Raw TCP
    .tcp_din        (tcp_din),
    .tcp_vin        (tcp_vin && tcp_cts),
    .tcp_cts        (tcp_cts),
    .tcp_snd        (tcp_snd),
  
    .tcp_dout       (tcp_dout),
    .tcp_vout       (tcp_vout),
  
    .rem_ipv4       (rem_ipv4),
    .loc_port       (loc_port),
    .rem_port       (rem_port),
    .connect        (connect),
    .connected      (connected),
    .listen         (listen),
    // Core status
    .ready          (ready),
    .error          (error),
    // DHCP related
    .preferred_ipv4 (preferred_ipv4),
    .assigned_ipv4  (assigned_ipv4),
    .dhcp_start     (dhcp_start),
    .dhcp_success   (dhcp_success),
    .dhcp_fail      (dhcp_fail)
  );
  
  always @ (posedge clk_125m) begin
    listen     <= ready;
    dhcp_start <= !ready;
  end

endmodule
