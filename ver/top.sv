module top
  import eth_vlg_pkg::*; #(
  parameter int                               N                            = 2,
  parameter mac_addr_t                        CLI_MAC_ADDR                 = {8'hde,8'had,8'hbe,8'hef,8'h00,8'h01},
  parameter mac_addr_t                        SRV_MAC_ADDR                 = {8'hde,8'had,8'hbe,8'hef,8'h00,8'h02},
  parameter int                               CLI_DOMAIN_NAME_LEN          = 32'd6,
  parameter int                               SRV_DOMAIN_NAME_LEN          = 32'd6,
  parameter int                               CLI_HOSTNAME_LEN             = 32'd8,
  parameter int                               SRV_HOSTNAME_LEN             = 32'd8,
  parameter int                               CLI_FQDN_LEN                 = 32'd8,
  parameter int                               SRV_FQDN_LEN                 = 32'd8,
  parameter int                               CLI_DUT_STRING_LEN           = 32'd3,
  parameter int                               SRV_DUT_STRING_LEN           = 32'd3,
  parameter [CLI_DOMAIN_NAME_LEN-1:0][7:0]    CLI_DOMAIN_NAME              = "dn_cli",
  parameter [SRV_DOMAIN_NAME_LEN-1:0][7:0]    SRV_DOMAIN_NAME              = "dn_srv",
  parameter [CLI_HOSTNAME_LEN-1:0]   [7:0]    CLI_HOSTNAME                 = "host_cli",
  parameter [SRV_HOSTNAME_LEN-1:0]   [7:0]    SRV_HOSTNAME                 = "host_srv",
  parameter [CLI_FQDN_LEN-1:0]       [7:0]    CLI_FQDN                     = "fqdn_cli",  
  parameter [SRV_FQDN_LEN-1:0]       [7:0]    SRV_FQDN                     = "fqdn_srv",
  parameter [CLI_DUT_STRING_LEN-1:0] [7:0]    CLI_DUT_STRING               = "cli",
  parameter [SRV_DUT_STRING_LEN-1:0] [7:0]    SRV_DUT_STRING               = "srv",
  parameter ipv4_t                            DEFAULT_GATEWAY              = {8'd192, 8'd168, 8'd0, 8'hd1}        ,
  parameter int                               MTU                          = 1080                                 ,
  parameter int                               TCP_RETRANSMIT_TICKS         = 12500                                ,
  parameter int                               TCP_RETRANSMIT_TRIES         = 5                                    ,
  parameter int                               TCP_SACK_RETRANSMIT_TICKS    = 75                                   ,
  parameter int                               TCP_FAST_RETRANSMIT_TICKS    = 500                                  ,
  parameter int                               TCP_RX_RAM_DEPTH             = 14                                   ,
  parameter int                               TCP_TX_RAM_DEPTH             = 14                                   ,
  parameter int                               TCP_PACKET_DEPTH             = 6                                    ,
  parameter int                               TCP_WAIT_TICKS               = 125                                  ,
  parameter int                               TCP_CONNECTION_TIMEOUT       = 125000                               ,
  parameter int                               TCP_ACK_TIMEOUT              = 12500                                ,
  parameter int                               TCP_DUP_ACKS                 = 5                                    ,
  parameter int                               TCP_FORCE_ACK_PACKETS        = 5                                    ,
  parameter int                               TCP_KEEPALIVE_PERIOD         = 600000000                            ,
  parameter int                               TCP_KEEPALIVE_INTERVAL       = 12500000                             ,
  parameter int                               TCP_ENABLE_KEEPALIVE         = 1                                    ,
  parameter int                               TCP_KEEPALIVE_TRIES          = 5                                    ,
  parameter int                               REFCLK_HZ                    = 5000                                 ,
  parameter int                               DHCP_TIMEOUT_SEC             = 30                                   ,
  parameter int                               DHCP_RETRIES                 = 3                                    ,
  parameter bit                               DHCP_ENABLE                  = 1                                    ,
  parameter int                               ARP_TABLE_SIZE               = 8                                    ,
  parameter int                               ARP_TIMEOUT_TICKS            = 20000                                ,
  parameter int                               ARP_TRIES                    = 5                                    ,
  parameter int                               MAC_CDC_FIFO_DEPTH           = 8                                    ,
  parameter int                               MAC_CDC_DELAY                = 3                                    ,
  parameter bit                               TCP_VERBOSE                  = 1'b1                                 ,
  parameter bit                               ICMP_VERBOSE                 = 1'b0                                 ,
  parameter bit                               ARP_VERBOSE                  = 1'b0                                 ,
  parameter bit                               DHCP_VERBOSE                 = 1'b0                                 ,
  parameter bit                               UDP_VERBOSE                  = 1'b0                                 ,
  parameter bit                               IPV4_VERBOSE                 = 1'b0                                 ,
  parameter bit                               MAC_VERBOSE                  = 1'b0
)
(
  input  logic           clk            ,
  input  logic           rst            ,
  input  logic           phy_rx_clk     ,
  input  logic           phy_rx_err     ,
  input  logic           phy_rx_val     ,
  input  logic     [7:0] phy_rx_dat     ,
  output logic           phy_tx_clk     ,
  output logic           phy_tx_err     ,
  output logic           phy_tx_val     ,
  output logic     [7:0] phy_tx_dat     ,

  input  logic     [7:0] tcp_din        [N],
  input  logic           tcp_vin        [N],
  output logic           tcp_cts        [N],
  input  logic           tcp_snd        [N],
  output logic     [7:0] tcp_dout       [N],
  output logic           tcp_vout       [N],
  input  ipv4_t          tcp_rem_ipv4   [N],
  input  port_t          tcp_rem_port   [N],
  input  port_t          tcp_loc_port   [N],
  input  logic           tcp_connect    [N],
  input  logic           tcp_listen     [N],
  output ipv4_t          tcp_con_ipv4   [N],
  output port_t          tcp_con_port   [N],
  input  length_t        udp_len        [N],
  input  logic     [7:0] udp_din        [N],
  input  logic           udp_vin        [N],
  output logic           udp_cts        [N],
  output logic     [7:0] udp_dout       [N],
  output logic           udp_vout       [N],
  input  port_t          udp_loc_port   [N],
  output ipv4_t          udp_ipv4_rx    [N],
  output port_t          udp_rem_port_rx[N],
  input  ipv4_t          udp_ipv4_tx    [N],
  input  port_t          udp_rem_port_tx[N],
  output logic           idle           [N],
  output logic           listening      [N],
  output logic           connecting     [N],
  output logic           connected      [N],
  output logic           disconnecting  [N],
  output logic           ready          [N],
  output logic           error          [N],
  input  ipv4_t          preferred_ipv4 [N],
  input  logic           dhcp_start     [N],
  output logic           dhcp_lease     [N],
  output ipv4_t          assigned_ipv4  [N]
  /*,
  // common parameters export
  output ipv4_t          default_gateway          ,
  output int             mtu                      ,
  output int             tcp_retransmit_ticks     ,
  output int             tcp_retransmit_tries     ,
  output int             tcp_sack_retransmit_ticks,
  output int             tcp_fast_retransmit_ticks,
  output int             tcp_rx_ram_depth         ,
  output int             tcp_tx_ram_depth         ,
  output int             tcp_packet_depth         ,
  output int             tcp_wait_ticks           ,
  output int             tcp_connection_timeout   ,
  output int             tcp_ack_timeout          ,
  output int             tcp_dup_acks             ,
  output int             tcp_force_ack_packets    ,
  output int             tcp_keepalive_period     ,
  output int             tcp_keepalive_interval   ,
  output int             tcp_enable_keepalive     ,
  output int             tcp_keepalive_tries      ,
  output int             dhcp_timeout             ,
  output int             dhcp_retries             ,
  output bit             dhcp_enable              ,
  output int             arp_table_size           ,
  output int             mac_cdc_fifo_depth       ,
  output int             mac_cdc_delay            ,
  output bit             tcp_verbose              ,
  output bit             icmp_verbose             ,
  output bit             arp_verbose              ,
  output bit             dhcp_verbose             ,
  output bit             udp_verbose              ,
  output bit             ipv4_verbose             ,
  output bit             mac_verbose              ,
  // client parameters export         
  output mac_addr_t                     mac_addr         ,
  output int                            domain_name_len  ,
  output int                            hostname_len     ,
  output int                            fqdn_len         ,
  output int                            dut_string_len   ,      
  output bit [DOMAIN_NAME_LEN-1:0][7:0] domain_name      ,
  output bit [HOSTNAME_LEN-1:0]   [7:0] hostname         ,
  output bit [FQDN_LEN-1:0]       [7:0] fqdn             ,
  output bit [DUT_STRING_LEN-1:0] [7:0] dut_string       
  */
);
/*
  always_comb begin
    mac_addr                  = MAC_ADDR                 ;
    domain_name_len           = DOMAIN_NAME_LEN          ;
    hostname_len              = HOSTNAME_LEN             ;
    fqdn_len                  = FQDN_LEN                 ;
    domain_name               = DOMAIN_NAME              ;
    hostname                  = HOSTNAME                 ;
    default_gateway           = DEFAULT_GATEWAY          ;
    mtu                       = MTU                      ;
    tcp_retransmit_ticks      = TCP_RETRANSMIT_TICKS     ;
    tcp_retransmit_tries      = TCP_RETRANSMIT_TRIES     ;
    tcp_fast_retransmit_ticks = TCP_FAST_RETRANSMIT_TICKS;
    tcp_rx_ram_depth          = TCP_RX_RAM_DEPTH         ;
    tcp_tx_ram_depth          = TCP_TX_RAM_DEPTH         ;
    tcp_packet_depth          = TCP_PACKET_DEPTH         ;
    tcp_wait_ticks            = TCP_WAIT_TICKS           ;
    tcp_connection_timeout    = TCP_CONNECTION_TIMEOUT   ;
    tcp_ack_timeout           = TCP_ACK_TIMEOUT          ;
    tcp_dup_acks              = TCP_DUP_ACKS             ;
    tcp_force_ack_packets     = TCP_FORCE_ACK_PACKETS    ;
    tcp_keepalive_period      = TCP_KEEPALIVE_PERIOD     ;
    tcp_keepalive_interval    = TCP_KEEPALIVE_INTERVAL   ;
    tcp_enable_keepalive      = TCP_ENABLE_KEEPALIVE     ;
    tcp_keepalive_tries       = TCP_KEEPALIVE_TRIES      ;
    dhcp_timeout              = DHCP_TIMEOUT_SEC         ;
    dhcp_retries              = DHCP_RETRIES             ;
    dhcp_enable               = DHCP_ENABLE              ;
    arp_table_size            = ARP_TABLE_SIZE           ;                    
    mac_cdc_fifo_depth        = MAC_CDC_FIFO_DEPTH       ;               
    mac_cdc_delay             = MAC_CDC_DELAY            ;          
    tcp_verbose               = TCP_VERBOSE              ;        
    icmp_verbose              = ICMP_VERBOSE             ;         
    arp_verbose               = ARP_VERBOSE              ;        
    dhcp_verbose              = DHCP_VERBOSE             ;         
    udp_verbose               = UDP_VERBOSE              ;        
    ipv4_verbose              = IPV4_VERBOSE             ;         
    mac_verbose               = MAC_VERBOSE              ;        
    dut_string                = DUT_STRING               ;
    dut_string_len            = DUT_STRING_LEN           ;    
  end
*/
  logic       cli_phy_rx_err, srv_phy_rx_err;
  logic       cli_phy_rx_val, srv_phy_rx_val;
  logic [7:0] cli_phy_rx_dat, srv_phy_rx_dat;
  logic       cli_phy_tx_err, srv_phy_tx_err;
  logic       cli_phy_tx_val, srv_phy_tx_val;
  logic [7:0] cli_phy_tx_dat, srv_phy_tx_dat;
  
  switch_sim #(
    .N   (3),
    .MTU (3000)
  ) switch_inst (
    .clk   (clk),
    .rst   (rst),
    .con   (connected == 2'b11),
    .din   ({cli_phy_tx_dat, srv_phy_tx_dat, phy_rx_dat}),
    .vin   ({cli_phy_tx_val, srv_phy_tx_val, phy_rx_val}),
    .dout  ({cli_phy_rx_dat, srv_phy_rx_dat, phy_tx_dat}),
    .vout  ({cli_phy_rx_val, srv_phy_rx_val, phy_tx_val})
  );

  eth_vlg #(
    .MAC_ADDR                  (CLI_MAC_ADDR             ),
    .DEFAULT_GATEWAY           (DEFAULT_GATEWAY          ),
    .MTU                       (MTU                      ),
    .TCP_RETRANSMIT_TICKS      (TCP_RETRANSMIT_TICKS     ),
    .TCP_SACK_RETRANSMIT_TICKS (TCP_SACK_RETRANSMIT_TICKS),
    .TCP_RETRANSMIT_TRIES      (TCP_RETRANSMIT_TRIES     ),
    .TCP_RX_RAM_DEPTH          (TCP_RX_RAM_DEPTH         ),
    .TCP_TX_RAM_DEPTH          (TCP_TX_RAM_DEPTH         ),
    .TCP_PACKET_DEPTH          (TCP_PACKET_DEPTH         ),
    .TCP_WAIT_TICKS            (TCP_WAIT_TICKS           ),
    .TCP_CONNECTION_TIMEOUT    (TCP_CONNECTION_TIMEOUT   ),
    .TCP_ACK_TIMEOUT           (TCP_ACK_TIMEOUT          ),
    .TCP_FORCE_ACK_PACKETS     (TCP_FORCE_ACK_PACKETS    ),
    .TCP_KEEPALIVE_PERIOD      (TCP_KEEPALIVE_PERIOD     ),
    .TCP_KEEPALIVE_INTERVAL    (TCP_KEEPALIVE_INTERVAL   ),
    .TCP_ENABLE_KEEPALIVE      (TCP_ENABLE_KEEPALIVE     ),
    .TCP_KEEPALIVE_TRIES       (TCP_KEEPALIVE_TRIES      ),
    .DOMAIN_NAME_LEN           (CLI_DOMAIN_NAME_LEN      ),
    .HOSTNAME_LEN              (CLI_HOSTNAME_LEN         ),
    .FQDN_LEN                  (CLI_FQDN_LEN             ),
    .DOMAIN_NAME               (CLI_DOMAIN_NAME          ),
    .HOSTNAME                  (CLI_HOSTNAME             ),
    .FQDN                      (CLI_FQDN                 ),
    .REFCLK_HZ                 (REFCLK_HZ                ),       
    .DHCP_TIMEOUT_SEC          (DHCP_TIMEOUT_SEC         ),       
    .DHCP_ENABLE               (DHCP_ENABLE              ),          
    .ARP_TABLE_SIZE            (ARP_TABLE_SIZE           ),
    .ARP_TIMEOUT_TICKS         (ARP_TIMEOUT_TICKS        ),
    .ARP_TRIES                 (ARP_TRIES                ),
    .MAC_CDC_FIFO_DEPTH        (MAC_CDC_FIFO_DEPTH       ),
    .MAC_CDC_DELAY             (MAC_CDC_DELAY            ),
    .ICMP_VERBOSE              (ICMP_VERBOSE             ),
    .TCP_VERBOSE               (TCP_VERBOSE              ),
    .ARP_VERBOSE               (ARP_VERBOSE              ),
    .DHCP_VERBOSE              (DHCP_VERBOSE             ),
    .UDP_VERBOSE               (UDP_VERBOSE              ),
    .IPV4_VERBOSE              (IPV4_VERBOSE             ),
    .MAC_VERBOSE               (MAC_VERBOSE              ),
    .DUT_STRING                (CLI_DUT_STRING           )
  ) cli (
    .clk             (clk),
    .rst             (rst),
    .phy_rx_clk      (phy_rx_clk         ),
    .phy_rx_err      (cli_phy_rx_err     ),
    .phy_rx_val      (cli_phy_rx_val     ),
    .phy_rx_dat      (cli_phy_rx_dat     ),
    .phy_tx_clk      (phy_tx_clk         ),
    .phy_tx_err      (cli_phy_tx_err     ),
    .phy_tx_val      (cli_phy_tx_val     ),
    .phy_tx_dat      (cli_phy_tx_dat     ),
    .tcp_din         (tcp_din         [0]),
    .tcp_vin         (tcp_vin         [0]),
    .tcp_cts         (tcp_cts         [0]),
    .tcp_snd         (tcp_snd         [0]),
    .tcp_dout        (tcp_dout        [0]),
    .tcp_vout        (tcp_vout        [0]),
    .udp_len         (udp_len         [0]),
    .udp_din         (udp_din         [0]),
    .udp_vin         (udp_vin         [0]),
    .udp_cts         (udp_cts         [0]),
    .udp_dout        (udp_dout        [0]),
    .udp_vout        (udp_vout        [0]),
    .udp_loc_port    (udp_loc_port    [0]),
    .udp_ipv4_rx     (udp_ipv4_rx     [0]),
    .udp_rem_port_rx (udp_rem_port_rx [0]),
    .udp_ipv4_tx     (udp_ipv4_tx     [0]),
    .udp_rem_port_tx (udp_rem_port_tx [0]),
    .tcp_rem_ipv4    (tcp_rem_ipv4    [0]),
    .tcp_rem_port    (tcp_rem_port    [0]),
    .tcp_loc_port    (tcp_loc_port    [0]),
    .tcp_con_port    (tcp_con_port    [0]),
    .tcp_con_ipv4    (tcp_con_ipv4    [0]),
    .tcp_connect     (tcp_connect     [0]),
    .tcp_listen      (tcp_listen      [0]),
    .idle            (idle            [0]),
    .listening       (listening       [0]),
    .connecting      (connecting      [0]),
    .connected       (connected       [0]),
    .disconnecting   (disconnecting   [0]),
    .ready           (ready           [0]),
    .error           (error           [0]),
    .preferred_ipv4  (preferred_ipv4  [0]),
    .dhcp_start      (dhcp_start      [0]),
    .assigned_ipv4   (assigned_ipv4   [0]),
    .dhcp_lease      (dhcp_lease      [0])
  );


  eth_vlg #(
    .MAC_ADDR                  (SRV_MAC_ADDR             ),
    .DEFAULT_GATEWAY           (DEFAULT_GATEWAY          ),
    .MTU                       (MTU                      ),
    .TCP_RETRANSMIT_TICKS      (TCP_RETRANSMIT_TICKS     ),
    .TCP_SACK_RETRANSMIT_TICKS (TCP_SACK_RETRANSMIT_TICKS),
    .TCP_RETRANSMIT_TRIES      (TCP_RETRANSMIT_TRIES     ),
    .TCP_RX_RAM_DEPTH          (TCP_RX_RAM_DEPTH         ),
    .TCP_TX_RAM_DEPTH          (TCP_TX_RAM_DEPTH         ),
    .TCP_PACKET_DEPTH          (TCP_PACKET_DEPTH         ),
    .TCP_WAIT_TICKS            (TCP_WAIT_TICKS           ),
    .TCP_CONNECTION_TIMEOUT    (TCP_CONNECTION_TIMEOUT   ),
    .TCP_ACK_TIMEOUT           (TCP_ACK_TIMEOUT          ),
    .TCP_FORCE_ACK_PACKETS     (TCP_FORCE_ACK_PACKETS    ),
    .TCP_KEEPALIVE_PERIOD      (TCP_KEEPALIVE_PERIOD     ),
    .TCP_KEEPALIVE_INTERVAL    (TCP_KEEPALIVE_INTERVAL   ),
    .TCP_ENABLE_KEEPALIVE      (TCP_ENABLE_KEEPALIVE     ),
    .TCP_KEEPALIVE_TRIES       (TCP_KEEPALIVE_TRIES      ),
    .DOMAIN_NAME_LEN           (SRV_DOMAIN_NAME_LEN      ),
    .HOSTNAME_LEN              (SRV_HOSTNAME_LEN         ),
    .FQDN_LEN                  (SRV_FQDN_LEN             ),
    .DOMAIN_NAME               (SRV_DOMAIN_NAME          ),
    .HOSTNAME                  (SRV_HOSTNAME             ),
    .FQDN                      (SRV_FQDN                 ),
    .REFCLK_HZ                 (REFCLK_HZ                ),       
    .DHCP_TIMEOUT_SEC          (DHCP_TIMEOUT_SEC         ),       
    .DHCP_ENABLE               (DHCP_ENABLE              ),          
    .ARP_TABLE_SIZE            (ARP_TABLE_SIZE           ),
    .ARP_TIMEOUT_TICKS         (ARP_TIMEOUT_TICKS        ),
    .ARP_TRIES                 (ARP_TRIES                ),
    .MAC_CDC_FIFO_DEPTH        (MAC_CDC_FIFO_DEPTH       ),
    .MAC_CDC_DELAY             (MAC_CDC_DELAY            ),
    .ICMP_VERBOSE              (ICMP_VERBOSE             ),
    .TCP_VERBOSE               (TCP_VERBOSE              ),
    .ARP_VERBOSE               (ARP_VERBOSE              ),
    .DHCP_VERBOSE              (DHCP_VERBOSE             ),
    .UDP_VERBOSE               (UDP_VERBOSE              ),
    .IPV4_VERBOSE              (IPV4_VERBOSE             ),
    .MAC_VERBOSE               (MAC_VERBOSE              ),
    .DUT_STRING                (SRV_DUT_STRING           )
  ) srv (
    .clk             (clk),
    .rst             (rst),
    .phy_rx_clk      (phy_rx_clk         ),
    .phy_rx_err      (srv_phy_rx_err     ),
    .phy_rx_val      (srv_phy_rx_val     ),
    .phy_rx_dat      (srv_phy_rx_dat     ),
    .phy_tx_clk      (phy_tx_clk         ),
    .phy_tx_err      (srv_phy_tx_err     ),
    .phy_tx_val      (srv_phy_tx_val     ),
    .phy_tx_dat      (srv_phy_tx_dat     ),
    .tcp_din         (tcp_din         [1]),
    .tcp_vin         (tcp_vin         [1]),
    .tcp_cts         (tcp_cts         [1]),
    .tcp_snd         (tcp_snd         [1]),
    .tcp_dout        (tcp_dout        [1]),
    .tcp_vout        (tcp_vout        [1]),
    .udp_len         (udp_len         [1]),
    .udp_din         (udp_din         [1]),
    .udp_vin         (udp_vin         [1]),
    .udp_cts         (udp_cts         [1]),
    .udp_dout        (udp_dout        [1]),
    .udp_vout        (udp_vout        [1]),
    .udp_loc_port    (udp_loc_port    [1]),
    .udp_ipv4_rx     (udp_ipv4_rx     [1]),
    .udp_rem_port_rx (udp_rem_port_rx [1]),
    .udp_ipv4_tx     (udp_ipv4_tx     [1]),
    .udp_rem_port_tx (udp_rem_port_tx [1]),
    .tcp_rem_ipv4    (tcp_rem_ipv4    [1]),
    .tcp_rem_port    (tcp_rem_port    [1]),
    .tcp_loc_port    (tcp_loc_port    [1]),
    .tcp_con_port    (tcp_con_port    [1]),
    .tcp_con_ipv4    (tcp_con_ipv4    [1]),
    .tcp_connect     (tcp_connect     [1]),
    .tcp_listen      (tcp_listen      [1]),
    .idle            (idle            [1]),
    .listening       (listening       [1]),
    .connecting      (connecting      [1]),
    .connected       (connected       [1]),
    .disconnecting   (disconnecting   [1]),
    .ready           (ready           [1]),
    .error           (error           [1]),
    .preferred_ipv4  (preferred_ipv4  [1]),
    .dhcp_start      (dhcp_start      [1]),
    .assigned_ipv4   (assigned_ipv4   [1]),
    .dhcp_lease      (dhcp_lease      [1])
  );

endmodule
