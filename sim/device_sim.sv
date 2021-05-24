import gateway_sim_pkg::*;
import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ipv4_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;
import dhcp_vlg_pkg::*;

module device_sim #(
  parameter mac_addr_t MAC_ADDRESS                     = 0,
  parameter ipv4_t     IPV4_ADDRESS                    = 0,
  parameter ipv4_t     DHCP_SERVER_IPV4_ADDRESS        = {8'd192, 8'd168, 8'd0,   8'd1},
  parameter ipv4_t     ROUTER_IPV4_ADDRESS             = {8'd192, 8'd168, 8'd0,   8'd1},
  parameter ipv4_t     SUBNET_MASK                     = {8'd255, 8'd255, 8'd255, 8'd0},
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
  
  gateway_c #(MAC_ADDRESS, IPV4_ADDRESS) device;
  initial device = new();
  
  byte packet_buff[$][];
  bit receiving;
  
  bit send;
  byte data_buff [$];
  byte data_rx [];
  byte data_tx [];
  byte cur_data_tx [];
  byte cur_tx_data_eth [];
  
  enum byte {idle_s, rx_s, parse_s, wait_rst_s} fsm_rx;
  
  task copy_from_buff;
    input  byte buff[$];
    output byte data[];
    data = new[buff.size()];
    data = buff;
  endtask : copy_from_buff
  
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
            data_buff.push_back(in.dat);
          end
          if (!in.val && receiving) begin
            copy_from_buff(data_buff, data_rx);
            data_buff.delete();
            fsm_rx = parse_s;
          end
        end
        parse_s : begin
          receiving = 0;
          fsm_rx = wait_rst_s;
          device.proc(data_rx, data_tx, send);
          data_rx.delete();
          packet_buff.push_front(data_tx);
        end
        wait_rst_s : begin
          fsm_rx = rx_s;
          send = 0;
        end
      endcase
    end
  end
  
  //////////////
  // Transmit //
  //////////////
  int ctr_tx;
  
  enum byte {tx_idle_s, tx_active_s, tx_wait_ifg_s} fsm_tx;
  parameter int IFG_TICKS = 10;
  byte ifg_ctr;
  always_ff @ (posedge clk_tx) begin
    if (rst_tx) begin
      out.val = 0;
      out.dat = 0;
      ctr_tx  = 0;
      ifg_ctr = 0;
      fsm_tx  = tx_idle_s;
    end
    else begin
      case (fsm_tx)
        tx_idle_s : begin
          if (packet_buff.size() != 0) begin
            cur_data_tx = packet_buff.pop_back();
            fsm_tx = tx_active_s;
          end
          ctr_tx = 0;
          ifg_ctr = 0;
        end
        tx_active_s : begin
          if (ctr_tx != cur_data_tx.size()) begin
            out.dat = cur_data_tx[ctr_tx];
            ctr_tx = ctr_tx + 1;
            out.val = 1;
          end
          else begin
            fsm_tx = tx_wait_ifg_s;
            out.val = 0;
            out.dat = 0;
          end
        end
        tx_wait_ifg_s : begin
          ifg_ctr = ifg_ctr + 1;
          if (ifg_ctr == IFG_TICKS) fsm_tx = tx_idle_s;
        end
      endcase
    end
  end

endmodule