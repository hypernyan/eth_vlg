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

`include "../../../esg_include/esg_reg_defines.sv"

parameter [3:0][7:0] PREFERRED_IPV4 = {8'd192, 8'd168, 8'd0, 8'd213};
parameter ESG_PRM_COUNT = 32;

logic arst;
assign arst = !reset_n;

phy phy_rx(.*);
phy phy_tx(.*);

logic [7:0] gmii_rx_dat, gmii_tx_dat;
logic       gmii_rx_val, gmii_tx_val;
logic       gmii_rx_err, gmii_tx_err;

logic clk_125m;
assign clk_125m = gen_clk_125m;

logic  [7:0] tcp_din;
logic        tcp_vin;
logic        tcp_cts;
logic        tcp_snd;
logic  [7:0] tcp_dout;
logic        tcp_vout;
ipv4_t       rem_ipv4;
port_t       rem_port;
logic        connect;
port_t       loc_port;
logic        listen;
logic        connected;

logic   ready;
logic   error;

ipv4_t  preferred_ipv4;
ipv4_t  assigned_ipv4;
logic   dhcp_success;
logic   dhcp_timeout;

assign loc_port = 1000;

assign preferred_ipv4 = PREFERRED_IPV4;

assign led[0] = ready;
assign led[1] = connected;

////////////////
// Speed test //
////////////////

/*
logic [7:0] ctr;
always @ (posedge clk_125m) begin
  ctr <= ctr + 1;
  if (tcp_cts && (ctr < 64)) begin
    tcp_vin <= 1;
    tcp_din <= tcp_din + 1;
  end
  else tcp_vin <= 0;
end
*/

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
  .DEFAULT_GATEWAY ({8'd192, 8'd168, 8'd0, 8'hd1}),
  .MTU             (9000),
    
  .TCP_RETRANSMIT_TICKS   (200000),
  .TCP_RETRANSMIT_TRIES   (5),
  .TCP_RAM_DEPTH          (15),
  .TCP_PACKET_DEPTH       (5),
  .TCP_WAIT_TICKS         (1000),
  .TCP_CONNECTION_TIMEOUT (125000000), 
  .TCP_ACK_TIMEOUT        (125000),    
  .TCP_KEEPALIVE_PERIOD   (600000000), 
  .TCP_KEEPALIVE_INTERVAL (60000),
  .TCP_ENABLE_KEEPALIVE   (1),
  .TCP_KEEPALIVE_TRIES    (5),

  .DOMAIN_NAME_LEN (5),
  .HOSTNAME_LEN    (8),
  .FQDN_LEN        (9),
  .DOMAIN_NAME     ("fpga0"),
  .HOSTNAME        ("fpga_eth"),
  .FQDN            ("fpga_host"),
  .DHCP_TIMEOUT    (125000000),
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

/////////
// esg //
/////////

ram_if_sp #(.AW(8), .DW(32)) ram (.*);
assign ram.clk = clk_125m;
exe #(.PRM_COUNT(ESG_PRM_COUNT)) exe_if(.*);

esg esg_inst (
  .clk    (clk_125m),
  .rst    (rst),

  .rxd    (tcp_dout),
  .rxv    (tcp_vout),

  .txd    (tcp_din),
  .txv    (tcp_vin),
  .cts    (tcp_cts),
 
  .ram    (ram),
  .exe_if (exe_if)
);


led_control led_control_inst (
  .clk          (clk_125m),
  .rst          (rst),
  .exe_if       (exe_if),
  .ram          (ram),
  .connected    (connected),
  .dhcp_success (dhcp_success),
  .dhcp_fail    (dhcp_fail),   
  .led          (led[3:2])
);

endmodule

module led_control #(
  parameter int REFCLK_HZ = 125000000
)
(
  input logic   clk,
  input logic   rst,
  exe.in        exe_if,
  ram_if_sp.sys ram,
  input logic   connected,   
  input logic   dhcp_success,
  input logic   dhcp_fail,   
  output logic [1:0] led
);

enum logic {stat, blink} mode;

logic led0_raw;
logic led1_raw;

always @ (posedge clk) begin
  if (rst) begin
    mode <= blink;
  end
  else begin
    if (exe_if.val) begin
      case (exe_if.addr)
        ADDR_BLINK_ON : begin
          mode <= blink;
        end      
        ADDR_ALL_ON : begin
          mode <= stat;
          led0_raw <= 1;
          led1_raw <= 1;
        end        
        ADDR_ALL_OFF : begin
          mode <= stat;
          led0_raw <= 0;
          led1_raw <= 0;
        end       
        ADDR_0_ON : begin
          mode <= stat;
          led0_raw <= 1;
        end          
        ADDR_0_OFF : begin
          mode <= stat;
          led0_raw <= 0;
        end         
        ADDR_1_ON : begin
          mode <= stat;
          led1_raw <= 1;
        end          
        ADDR_1_OFF : begin
          mode <= stat;
          led1_raw <= 0;
        end         
      endcase
    end
  end
end

logic [$clog2(100)-1:0] brightness;
logic [$clog2(2500)-1:0] period;
logic [$clog2(2500)-1:0] ctr_blink;

logic [7:0] ram_a_dl;

always @ (posedge clk) begin
  if (rst) begin

  end
  else begin
    ram.a <= (ram.a == STOP_ADDR) ? START_ADDR : ram.a + 1;
    ram_a_dl <= ram.a;
    case (ram_a_dl)
      ADDR_LED_BRIGHTNESS : brightness <= ram.q;
      ADDR_LED_PERIOD : period <= ram.q;
    endcase
  end
end

always @ (posedge clk) begin
  if (rst) begin

  end
  else begin
    case (mode)
      stat : begin
        led[0] <= led0_raw;
        led[1] <= led1_raw;
      end
      blink : begin
        ctr_blink <= (tick_1ms) ? (ctr_blink == period) ? 0 : ctr_blink + 1 : ctr_blink;
        if (tick_1ms && (ctr_blink == 0)) begin
          led[0] <= !led[0];
          led[1] <= !led[1];
        end
      end
    endcase
  end
end

logic tick_1ms;
logic [$clog2((REFCLK_HZ/1000)+1):0] ctr_1ms;

always @ (posedge clk) begin
  if (ctr_1ms == ((REFCLK_HZ/1000)-1)) begin
    ctr_1ms <= 0;
    tick_1ms <= 1;
  end
  else begin
    ctr_1ms <= ctr_1ms + 1;
    tick_1ms <= 0;
  end
end

endmodule : led_control