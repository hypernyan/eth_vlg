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

byte data_in [];
byte data_out [$];

icmp_hdr_t      icmp_hdr;
bit             icmp_ok;
udp_hdr_t       udp_hdr;
bit             udp_ok;
tcp_hdr_t       tcp_hdr;
tcp_opt_hdr_t   tcp_opt_hdr;
bit             tcp_ok;
ipv4_hdr_t      ipv4_hdr;
bit             ipv4_ok;
arp_hdr_t       arp_hdr;
bit             arp_ok;
dhcp_hdr_t      dhcp_hdr;
dhcp_opt_hdr_t  dhcp_opt_hdr;
dhcp_opt_pres_t dhcp_opt_pres;
dhcp_opt_len_t  dhcp_opt_len;
bit             dhcp_ok;
mac_hdr_t       mac_hdr;
bit             ok;

bit receiving;
bit timed_out;
wire nya;

byte data_queue [$];
byte data_rx [];
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
		      copy_from_queue(data_queue, data_rx);
          data_queue.delete();
		      fsm_rx <= parse_s;
		    end
      end
      parse_s : begin
		    receiving <= 0;
        device.parse (
		      data_rx,
          data_ipv4, 
          data, 
          icmp_hdr, 
          icmp_ok,
          udp_hdr, 
          udp_ok,
          tcp_hdr,
          tcp_opt_hdr,
          tcp_ok,
          ipv4_hdr,
          ipv4_ok,
          arp_hdr,
          arp_ok,
          mac_hdr,
          dhcp_hdr,
          dhcp_opt_hdr,
          dhcp_opt_pres,
          dhcp_opt_len,
          dhcp_ok,
          ok
		    );
          $display("Got DHCP packet: %d", dhcp_opt_hdr.dhcp_opt_message_type);
        if (dhcp_ok) begin
         device.gen_dhcp_pkt(dhcp_hdr, dhcp_opt_hdr, dhcp_opt_pres, dhcp_opt_len, data_out);
          $display("Generated DHCP packet: %p", data_out);
          len = data_out.size();
        end
		    fsm_rx <= wait_rst_s;
	    end
	    wait_rst_s : begin
        ctr <= ctr + 1;
        phy_out_d <= data_out[ctr];
        phy_out_v <= ctr < len;
	      icmp_ok <= 0;
	      udp_ok  <= 0;
	      tcp_ok  <= 0;
		    ipv4_ok <= 0;
		    arp_ok  <= 0;
	    end
    endcase
  end
end

enum byte {engine_idle_s, arp_request_s, arp_reply_s, icmp_request_s, icmp_reply_s} engine_fsm;
/*byte ctr;
always @ (posedge clk_rx) begin
  if (rst_rx) begin
    engine_fsm <= engine_idle_s;
    ctr = 0;
  end
  else begin
	case (engine_fsm)
    engine_idle_s : begin
      phy_out_v = 0;
      phy_out_d = 0;
	    if (arp_ok) begin
		  case (arp_hdr.oper)
        1 : begin // Request
			  // Got a request. Generate a reply now
		      device.gen_arp_reply(arp_hdr.src_ipv4_addr, arp_hdr.src_mac_addr, data_tx);
          engine_fsm <= arp_request_s;
		    end
		      2 : begin // Reply
		        // Reply with nothing. ARP table updated automatically in arp_parse
		      end 
		    endcase
		end
		if (icmp_ok) begin
		  
		end
	  end
	  arp_request_s : begin  
      phy_out_v = 1;
      phy_out_d = data_tx[ctr];
      ctr = ctr + 1;
      if (ctr == data_tx.size()) engine_fsm <= engine_idle_s;
	  end
	  arp_reply_s : begin
        
	  end
	  icmp_request_s : begin
        
	  end
	  icmp_reply_s : begin
        
	  end
	endcase
  end
end
*/
endmodule