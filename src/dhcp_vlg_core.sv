import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;
import dhcp_vlg_pkg::*;

module dhcp_vlg_core #(
  parameter mac_addr_t MAC_ADDR = 0
)
(
  input logic clk,
  input logic rst,

  input  logic  ipv4_req,
  input  ipv4_t ipv4_addr,
  output logic  ipv4_addr_val,
  output logic  ipv4_addr_timeout,
  input  dev_t  dev,
  output logic  ok,
  output logic  timeout,
  dhcp.in       rx,
  dhcp.out      tx
);
logic fsm_rst;
assign fsm_rst = rst;

enum logic [4:0] {idle_s, discover_s, offer_s, request_s, ack_s} fsm;

always @ (posedge clk) begin
  if (fsm_rst) begin
    fsm <= idle_s;
    tx.hdr <= 0;
    tx.opt_hdr <= 0;
    tx.opt_pres <= 0;
    tx.val <= 0;
  end
  else begin
    case (fsm)
      idle_s : begin
        if (ipv4_req) fsm <= discover_s;
      end
      discover_s : begin
        tx.val <= 1;

        tx.hdr.dhcp_op           <= dhcp_vlg_pkg::DHCP_MSG_TYPE_DISCOVER;
        tx.hdr.dhcp_htype        <= 1;
        tx.hdr.dhcp_hlen         <= 6;
        tx.hdr.dhcp_hops         <= 0;
        tx.hdr.dhcp_xid          <= 32'hdeadface;
        tx.hdr.dhcp_secs         <= 0; 
        tx.hdr.dhcp_flags        <= 0;
        tx.hdr.dhcp_cur_cli_addr <= 0; 
        tx.hdr.dhcp_nxt_cli_addr <= 0; 
        tx.hdr.dhcp_srv_ip_addr  <= 0; 
        tx.hdr.dhcp_retrans_addr <= 0; 
        tx.hdr.dhcp_chaddr       <= {MAC_ADDR, {9{8'h00}}};
        tx.hdr.dhcp_sname        <= 0;
        tx.hdr.dhcp_file         <= 0;
        tx.hdr.dhcp_cookie       <= dhcp_vlg_pkg::DHCP_COOKIE;
        
        tx.opt_hdr.dhcp_opt_message_type             <= dhcp_vlg_pkg::DHCP_MSG_TYPE_DISCOVER;
        tx.opt_hdr.dhcp_opt_subnet_mask              <= 0;
        tx.opt_hdr.dhcp_opt_renewal_time             <= 0;
        tx.opt_hdr.dhcp_opt_rebinding_time           <= 0;
        tx.opt_hdr.dhcp_opt_ip_addr_lease_time       <= 0;
        tx.opt_hdr.dhcp_opt_dhcp_server_id           <= 0;
        tx.opt_hdr.dhcp_opt_dhcp_client_id           <= dev.ipv4_addr;
        tx.opt_hdr.dhcp_opt_router                   <= 0;
        tx.opt_hdr.dhcp_opt_domain_name_server       <= 0;
        tx.opt_hdr.dhcp_opt_domain_name              <= 0;
        tx.opt_hdr.dhcp_opt_fully_qualified_domain_name <= {8'hcc, 8'hdd, 8'hee};
        
        tx.opt_pres.dhcp_opt_message_type_pres       <= 1;
        tx.opt_pres.dhcp_opt_subnet_mask_pres        <= 0;
        tx.opt_pres.dhcp_opt_renewal_time_pres       <= 0;
        tx.opt_pres.dhcp_opt_rebinding_time_pres     <= 0;
        tx.opt_pres.dhcp_opt_ip_addr_lease_time_pres <= 0;
        tx.opt_pres.dhcp_opt_dhcp_server_id_pres     <= 0;
        tx.opt_pres.dhcp_opt_dhcp_client_id_pres     <= 0;
        tx.opt_pres.dhcp_opt_router_pres             <= 0;
        tx.opt_pres.dhcp_opt_domain_name_server_pres <= 0;
        tx.opt_pres.dhcp_opt_domain_name_pres        <= 0;
        fsm <= offer_s;
      end
      offer_s : begin
        tx.val <= 0;
      end
      request_s : begin
        
      end
      ack_s : begin
        
      end
    endcase
  end
end
endmodule : dhcp_vlg_core