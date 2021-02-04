import eth_vlg_sim::*;
import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;
import dhcp_vlg_pkg::*;

module device_sim #(
  parameter mac_addr_t MAC_ADDRESS = 0,
  parameter ipv4_t     IPV4_ADDRESS = 0
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
device_c device = new(MAC_ADDRESS, IPV4_ADDRESS);

byte phy_in_d;
bit  phy_in_v;
byte phy_out_d;
bit  phy_out_v;

byte rx_data [];
byte data_out [$];

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

bit receiving;
bit timed_out;
wire nya;

byte data_queue [$];
byte rx_data_eth [];
byte data_tx [];
byte data_parsed [];
byte data_ipv4  []; 
byte data  []; 

enum byte {idle_s, rx_s, parse_s, wait_rst_s} fsm_rx;

assign phy_in_d = in.d;
assign phy_in_v = in.v;

assign out.d = phy_out_d;
assign out.v = phy_out_v;

task copy_from_queue;
  input  byte queue[$];
  output byte data[];
  data = new[queue.size()];
  data = queue;
endtask : copy_from_queue

logic [15:0] ctr, len;

always @(posedge clk_rx) begin
  if (rst_rx) begin
    fsm_rx <= rx_s;
  receiving <= 0;
  ctr <= 0;
  end
  else begin
    case (fsm_rx)
      rx_s : begin
        if (in.v) begin
          receiving <= 1;
          data_queue.push_back(in.d);
        end
        if (!in.v && receiving) begin
          copy_from_queue(data_queue, rx_data_eth);
          data_queue.delete();
          fsm_rx <= parse_s;
        end
      end
      parse_s : begin
        receiving <= 0;
        device.parse (
          rx_data_eth, // ethernet frame
          rx_data,     // payload. proto varies
          rx_mac_hdr,  // mac header
          rx_ok,
          // arp
          rx_arp_hdr,
          rx_arp_ok,
          // ipv4
          rx_ipv4_hdr,
          rx_ipv4_ok,
          // icmp
          rx_icmp_hdr, 
          rx_icmp_ok,
          // tcp
          rx_tcp_hdr,
          rx_tcp_opt_hdr,
          rx_tcp_ok,
          // udp
          rx_udp_hdr, 
          rx_udp_ok,
          // dhcp
          rx_dhcp_hdr,
          rx_dhcp_opt_hdr,
          rx_dhcp_opt_pres,
          rx_dhcp_opt_len,
          rx_dhcp_ok
        );
        fsm_rx <= wait_rst_s;
      end
      wait_rst_s : begin
        rx_ok      <= 0;
        rx_arp_ok  <= 0;
        rx_ipv4_ok <= 0;
        rx_icmp_ok <= 0;
        rx_tcp_ok  <= 0;
        rx_udp_ok  <= 0;
        rx_dhcp_ok <= 0;
      end
    endcase
  end
end

enum byte {engine_idle_s, arp_request_s, arp_reply_s, icmp_request_s, icmp_reply_s} engine_fsm;


always @ (posedge clk_rx) begin
  if (rst_rx) begin
  end
  else begin
    phy_out_v = 0;
    phy_out_d = 0;
    if (rx_dhcp_ok) begin
      $display("A DHCP packet from %h:%h:%h:%h:%h:%h", 
        rx_mac_hdr.src_mac_addr[5],
        rx_mac_hdr.src_mac_addr[4],
        rx_mac_hdr.src_mac_addr[3],
        rx_mac_hdr.src_mac_addr[2],
        rx_mac_hdr.src_mac_addr[1],
        rx_mac_hdr.src_mac_addr[0]
      );
    //  case (rx_dhcp_hdr.)
    end
    if (rx_arp_ok) begin
      case (rx_arp_hdr.oper)
        1 : begin // Request
        // Got a request. Generate a reply now
          device.gen_arp_reply(rx_arp_hdr.src_ipv4_addr, rx_arp_hdr.src_mac_addr, data_tx);
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

endmodule

module eth_switch_sim #(
  parameter int N = 3,
  parameter int D = 12
)(
  input logic clk,
  input logic rst,

  input logic [7:0][N-1:0] din,
  input logic      [N-1:0] vin,

  output logic [7:0][N-1:0] dout,
  output logic      [N-1:0] vout
);

logic rdy;
logic [N-1:0]       act_ms;
logic [N-1:0]       fifo_r;
logic [N-1:0] [7:0] fifo_o;
logic [N-1:0]       fifo_v;
logic [N-1:0]       fifo_e;
logic [N-1:0]       fifo_f;
logic [N-1:0]       cur;
logic [N-1:0]       avl_v;

wor [$clog2(N+1)-1:0] ind;


genvar i;

generate
  for (i = 0; i < N; i = i + 1) begin : gen
    fifo_sc_no_if #(D, 8) fifo_inst (
      .rst      (rst),
      .clk      (clk),
      .write    (vin[i] && !fifo_f[i]),
      .data_in  (din[i]),

      .read      (fifo_r[i] && !fifo_e[i]),
      .data_out  (fifo_o[i]),
      .valid_out (fifo_v[i]),

      .full     (fifo_f[i]),
      .empty    (fifo_e[i])
    );
    always @ (posedge clk) if (rst) cur[i] <= 0; else cur[i] <= (rdy) ? ((!fifo_e[i] && fifo_r[i]) || act_ms[i]) : (cur[i] && !fifo_e[i]);
    assign ind = (fifo_r[i] == 1'b1) ? i : 0;
    always @ (posedge clk) if (rst) avl_v[i] <= 0; else avl_v[i] <= ~fifo_e[i]; // fifo is available to read if it is not empty
    assign dout[i] = fifo_o[ind];
    assign vout[i] = fifo_v[ind];
  end
endgenerate

onehot #(N, 1) onehot_msb_inst (
  .i (avl_v),
  .o (act_ms)
);

onehot #(N, 0) onehot_lsb_inst (
  .i (cur),
  .o (fifo_r)
);

endmodule