import gateway_sim_pkg::*;
import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;
import dhcp_vlg_pkg::*;

module device_sim #(
  parameter mac_addr_t MAC_ADDRESS  = 0,
  parameter ipv4_t     IPV4_ADDRESS = 0,
  parameter ipv4_t     DHCP_SERVER_IPV4_ADDRESS = {8'd192, 8'd168, 8'd0, 8'd1},
  parameter ipv4_t     ROUTER_IPV4_ADDRESS = {8'd192, 8'd168, 8'd0, 8'd1},
  parameter ipv4_t     SUBNET_MASK  = {8'd192, 8'd168, 8'd0, 8'd20},
  parameter [7:0]                      DOMAIN_NAME_LEN = 5,
  parameter [7:0]                      HOSTNAME_LEN    = 8,
  parameter [7:0]                      FQDN_LEN        = 9,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME     = "fpga0",
  parameter [0:HOSTNAME_LEN-1]  [7:0]  HOSTNAME        = "fpga_eth",
  parameter [0:FQDN_LEN-1]      [7:0]  FQDN            = "fpga_host"
)
(
  phy.in  in,
  phy.out out,
  input logic clk_rx,
  input logic clk_tx,
  input logic rst_rx,
  input logic rst_tx
);

parameter int DEFAULT_TIMEOUT = 10000000;

//device_c   device   = new(MAC_ADDRESS, IPV4_ADDRESS);
//dhcp_srv_c dhcp_srv = new(SUBNET_MASK);

byte phy_out_d;
bit  phy_out_v;

byte rx_data [];
byte data_out [$];

gateway_c #(MAC_ADDRESS, IPV4_ADDRESS) device;
initial device = new();

icmp_hdr_t      rx_icmp_hdr;
bit             rx_icmp_ok;
udp_hdr_t       rx_udp_hdr;
bit             rx_udp_ok;
tcp_hdr_t       rx_tcp_hdr;
tcp_opt_hdr_t   rx_tcp_opt_hdr;
bit             rx_tcp_ok;
ipv4_hdr_t      rx_ipv4_hdr;
bit             rx_ipv4_ok;
arp_hdr_t       rx_arp_hdr;
bit             rx_arp_ok;
dhcp_hdr_t      rx_dhcp_hdr;
dhcp_opt_hdr_t  rx_dhcp_opt_hdr;
dhcp_opt_pres_t rx_dhcp_opt_pres;
dhcp_opt_len_t  rx_dhcp_opt_len;
bit             rx_dhcp_ok;
mac_hdr_t       rx_mac_hdr;
bit             rx_ok;

icmp_hdr_t      tx_icmp_hdr;
udp_hdr_t       tx_udp_hdr;
tcp_hdr_t       tx_tcp_hdr;
tcp_opt_hdr_t   tx_tcp_opt_hdr;
ipv4_hdr_t      tx_ipv4_hdr;
arp_hdr_t       tx_arp_hdr;

mac_hdr_t       tx_mac_hdr;

bit receiving;
bit timed_out;

bit tx_val;
byte data_queue [$];
byte rx_data_eth [];
byte tx_data_eth [];
byte data_tx [];
byte data_parsed [];
byte data_ipv4  []; 
byte data  []; 

enum byte {idle_s, rx_s, parse_s, wait_rst_s} fsm_rx;

assign phy_in_d = in.dat;
assign phy_in_v = in.val;

assign out.dat = phy_out_d;
assign out.val = phy_out_v;

task copy_from_queue;
  input  byte queue[$];
  output byte data[];
  data = new[queue.size()];
  data = queue;
endtask : copy_from_queue

logic [15:0] ctr, len;
/////////////
// Receive //
/////////////
always @(posedge clk_rx) begin
  if (rst_rx) begin
    fsm_rx    = rx_s;
    receiving = 0;
    ctr       = 0;
  end
  else begin
    case (fsm_rx)
      rx_s : begin
        if (in.val) begin
          receiving = 1;
          data_queue.push_back(in.dat);
        end
        if (!in.val && receiving) begin
          copy_from_queue(data_queue, rx_data_eth);
          data_queue.delete();
          fsm_rx = parse_s;
        end
      end
      parse_s : begin
        receiving = 0;
        fsm_rx = wait_rst_s;
        device.proc (
          rx_data_eth, // ethernet frame
          tx_data_eth,     // payload. proto varies
          tx_val);  // mac header
        //  rx_ok,
        //  // arp
        //  rx_arp_hdr,
        //  rx_arp_ok,
        //  // ipv4
        //  rx_ipv4_hdr,
        //  rx_ipv4_ok,
        //  // icmp
        //  rx_icmp_hdr, 
        //  rx_icmp_ok,
        //  // tcp
        //  rx_tcp_hdr,
        //  rx_tcp_opt_hdr,
        //  rx_tcp_ok,
        //  // udp
        //  rx_udp_hdr, 
        //  rx_udp_ok,
        //  // dhcp
        //  rx_dhcp_hdr,
        //  rx_dhcp_opt_hdr,
        //  rx_dhcp_opt_pres,
        //  rx_dhcp_opt_len,
        //  rx_dhcp_ok
      end
      wait_rst_s : begin
        rx_ok      = 0;
        rx_arp_ok  = 0;
        rx_ipv4_ok = 0;
        rx_icmp_ok = 0;
        rx_tcp_ok  = 0;
        rx_udp_ok  = 0;
        rx_dhcp_ok = 0;
        fsm_rx = rx_s;

      end
    endcase
  end
end

/////////////
// Process //
/////////////

enum byte {engine_idle_s, arp_request_s, arp_reply_s, icmp_request_s, icmp_reply_s} engine_fsm;

bit dhcp_full;
bit dhcp_found;
int dhcp_index;

//dhcp_state_t dhcp_state;
dhcp_hdr_t tx_dhcp_hdr;
dhcp_opt_hdr_t tx_dhcp_opt_hdr;
dhcp_opt_pres_t tx_dhcp_opt_pres;
dhcp_opt_len_t tx_dhcp_opt_len;

always @ (posedge clk_rx) begin
  if (rst_rx) begin
  end
  else begin
    phy_out_v = 0;
    phy_out_d = 0;
    //////////
    // DHCP //
    //////////
  //  if (rx_dhcp_ok) begin
  //    $display ("A DHCP packet from %h:%h:%h:%h:%h:%h", 
  //      rx_mac_hdr.src_mac_addr[5],
  //      rx_mac_hdr.src_mac_addr[4],
  //      rx_mac_hdr.src_mac_addr[3],
  //      rx_mac_hdr.src_mac_addr[2],
  //      rx_mac_hdr.src_mac_addr[1],
  //      rx_mac_hdr.src_mac_addr[0]
  //    );
  //    device.dhcp_dev.proc(
  //      rx_mac_hdr,
  //      rx_dhcp_hdr,
  //      rx_dhcp_opt_hdr,
  //      rx_dhcp_opt_pres,
  //      rx_dhcp_opt_len,
 //
  //      tx_mac_hdr,
  //      tx_dhcp_hdr,
  //      tx_dhcp_opt_hdr,
  //      tx_dhcp_opt_pres,
  //      tx_dhcp_opt_len,
  //      tx_dhcp_val
  //    );
  //    if (tx_dhcp_val) device.dhcp_dev.dhcp_gen(
  //      tx_dhcp_hdr,
  //      tx_dhcp_opt_hdr,
  //      tx_dhcp_opt_pres,
  //      tx_dhcp_opt_len,
  //      tx_data
  //    );
  //    $display("tx_data %p", tx_data);
  //  end
    /////////
    // ARP //
    /////////
    if (rx_arp_ok) begin
      case (rx_arp_hdr.oper)
        1 : begin // Request
        // Got a request. Generate a reply now
          //device.gen_arp_reply(rx_arp_hdr.src_ipv4_addr, rx_arp_hdr.src_mac_addr, data_tx);
        end
        2 : begin // Reply
          // Reply with nothing. ARP table updated automatically in arp_parse
        end 
      endcase
    end
    if (rx_icmp_ok) begin
      case (rx_icmp_hdr.icmp_type)
        0 : begin
          
        end
        1 : begin
          
        end
      endcase
    end
  end
end
//////////////
// Transmit //
//////////////
/*
always @ (posedge tx_clk) begin
  if (tx_en) begin
    device.gen(
      data_in,
      data,   
      mac_hdr,
      val,
      arp_hdr,
      arp_val,
      ipv4_hdr,
      ipv4_val,
      icmp_hdr,
      icmp_val,
      tcp_hdr,
      tcp_opt_hdr,
      tcp_val,
      udp_hdr,
      udp_val,
      dhcp_hdr,
      dhcp_opt_hdr,
      dhcp_opt_pres,
      dhcp_opt_len,
      dhcp_val
    );
  end
end

*/
endmodule