import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;
import dhcp_vlg_pkg::*;

module dhcp_vlg_core #(
  parameter mac_addr_t                 MAC_ADDR        = 0,
  parameter [7:0]                      HOSTNAME_LEN    = 0,
  parameter [7:0]                      DOMAIN_NAME_LEN = 0,
  parameter [7:0]                      FQDN_LEN        = 0,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME     = "",
  parameter [0:HOSTNAME_LEN-1]   [7:0] HOSTNAME        = "",
  parameter [0:FQDN_LEN-1]       [7:0] FQDN            = "",
  parameter int                        TIMEOUT         = 1250000000,
  parameter bit                        ENABLE          = 1,
  parameter int                        RETRIES         = 3,
  parameter bit                        VERBOSE         = 1
)
(
  input  logic  clk,
  input  logic  rst,

  dhcp_ctrl.in  ctrl,
  dhcp.in       rx,
  dhcp.out      tx
);

  logic fsm_rst;
  
  enum logic [4:0] {idle_s, discover_s, offer_s, request_s, ack_s} fsm;
  
  ipv4_t offered_ip;
  ipv4_t server_ip; 
  logic timeout, enable;
  
  logic [$clog2(TIMEOUT+1)-1:0] timeout_ctr;
  logic [$clog2(RETRIES+1)-1:0] try_cnt;
  
  logic [31:0] xid_prng, dhcp_xid;
  prng prng_dhcp_xid_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (xid_prng)
  );
  
  ipv4_vlg_pkg::id_t ipv4_id;
  prng #(.W (16), .POLY (16'hface)) prng_ipv4_id_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (ipv4_id)
  );
  
  always @ (posedge clk) begin
    if (fsm_rst) begin
      fsm                  <= idle_s;
      tx.hdr               <= 0;
      tx.opt_hdr           <= 0;
      tx.opt_pres          <= 0;
      tx.val               <= 0;
      timeout_ctr          <= 0;
      timeout              <= 0;
      ctrl.assig_ip        <= 0;
      ctrl.router_ipv4_addr_val <= 0;
      ctrl.subnet_mask_val      <= 0;
      ctrl.router_ipv4_addr_val     <= 0;
      ctrl.success              <= 0;
      ctrl.subnet_mask          <= 0;
      tx.ipv4_id           <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (enable) begin
            fsm <= discover_s;
          end
        end
        discover_s : begin
          dhcp_xid                 <= xid_prng;
          ctrl.success             <= 0;
          tx.val                   <= 1;
          tx.hdr.dhcp_op           <= dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REQUEST;
          tx.hdr.dhcp_htype        <= 1;
          tx.hdr.dhcp_hlen         <= 6;
          tx.hdr.dhcp_hops         <= 0;
          tx.hdr.dhcp_xid          <= xid_prng;
          tx.hdr.dhcp_secs         <= 0; 
          tx.hdr.dhcp_flags        <= 16'h8000;
          tx.hdr.dhcp_cur_cli_addr <= 0; 
          tx.hdr.dhcp_nxt_cli_addr <= 0; 
          tx.hdr.dhcp_srv_ip_addr  <= 0; 
          tx.hdr.dhcp_retrans_addr <= 0; 
          tx.hdr.dhcp_chaddr       <= {MAC_ADDR, {10{8'h00}}};
          tx.hdr.dhcp_sname        <= 0;
          tx.hdr.dhcp_file         <= 0;
          tx.hdr.dhcp_cookie       <= dhcp_vlg_pkg::DHCP_COOKIE;
          
          tx.opt_hdr.dhcp_opt_message_type                      <= dhcp_vlg_pkg::DHCP_MSG_TYPE_DISCOVER;
          tx.opt_hdr.dhcp_opt_subnet_mask                       <= 0;
          tx.opt_hdr.dhcp_opt_renewal_time                      <= 0;
          tx.opt_hdr.dhcp_opt_rebinding_time                    <= 0;
          tx.opt_hdr.dhcp_opt_ip_addr_lease_time                <= 0;
          tx.opt_hdr.dhcp_opt_requested_ip_address              <= ctrl.pref_ip;
          tx.opt_hdr.dhcp_opt_dhcp_server_id                    <= 0;
          tx.opt_hdr.dhcp_opt_dhcp_client_id                    <= {1'b1, MAC_ADDR};
          tx.opt_hdr.dhcp_opt_router                            <= 0;
          tx.opt_hdr.dhcp_opt_domain_name_server                <= 0;
          tx.opt_hdr.dhcp_opt_hostname                          <= HOSTNAME;
          tx.opt_hdr.dhcp_opt_domain_name                       <= DOMAIN_NAME;
          tx.opt_hdr.dhcp_opt_fully_qualified_domain_name       <= FQDN;
          
          tx.opt_len.dhcp_opt_hostname_len                      <= HOSTNAME_LEN; 
          tx.opt_len.dhcp_opt_domain_name_len                   <= DOMAIN_NAME_LEN; 
          tx.opt_len.dhcp_opt_fully_qualified_domain_name_len   <= FQDN_LEN;
  
          tx.opt_pres.dhcp_opt_message_type_pres                <= 1;
          tx.opt_pres.dhcp_opt_subnet_mask_pres                 <= 0;
          tx.opt_pres.dhcp_opt_renewal_time_pres                <= 0;
          tx.opt_pres.dhcp_opt_rebinding_time_pres              <= 0;
          tx.opt_pres.dhcp_opt_ip_addr_lease_time_pres          <= 0;
          tx.opt_pres.dhcp_opt_requested_ip_address_pres        <= 1;
          tx.opt_pres.dhcp_opt_dhcp_server_id_pres              <= 0;
          tx.opt_pres.dhcp_opt_dhcp_client_id_pres              <= 1;
          tx.opt_pres.dhcp_opt_router_pres                      <= 0;
          tx.opt_pres.dhcp_opt_domain_name_server_pres          <= 0;
          tx.opt_pres.dhcp_opt_hostname_pres                    <= 1;
          tx.opt_pres.dhcp_opt_domain_name_pres                 <= 0;
          tx.opt_pres.dhcp_opt_fully_qualified_domain_name_pres <= 1;
          tx.opt_pres.dhcp_opt_end_pres                         <= 1;
          
          tx.src_ip                                             <= {8'h0,  8'h0,  8'h0,  8'h0};
          tx.dst_ip                                             <= {8'hff, 8'hff, 8'hff, 8'hff};
          tx.ipv4_id                                            <= ipv4_id;
          fsm <= offer_s;
          if (VERBOSE) $display("[DUT]-> DHCP discover. Preferred IP: %d.%d.%d.%d", 
            ctrl.pref_ip[3], 
            ctrl.pref_ip[2],
            ctrl.pref_ip[1],
            ctrl.pref_ip[0]
          );
        end
        offer_s : begin
          tx.val <= 0;
          timeout_ctr <= timeout_ctr + 1;
          if (timeout_ctr == TIMEOUT) timeout <= 1;
          if (rx.val) begin
            if (rx.hdr.dhcp_xid == dhcp_xid &&
                rx.hdr.dhcp_op == dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY &&
                rx.opt_pres.dhcp_opt_message_type_pres &&
                rx.opt_hdr.dhcp_opt_message_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_OFFER
            ) begin
              if (VERBOSE) $display("[DUT]<- DHCP offer. Offered IP: %d.%d.%d.%d, Server IP: %d.%d.%d.%d.",
                rx.hdr.dhcp_nxt_cli_addr[3],
                rx.hdr.dhcp_nxt_cli_addr[2],
                rx.hdr.dhcp_nxt_cli_addr[1],
                rx.hdr.dhcp_nxt_cli_addr[0],
                rx.hdr.dhcp_srv_ip_addr[3],
                rx.hdr.dhcp_srv_ip_addr[2],
                rx.hdr.dhcp_srv_ip_addr[1],
                rx.hdr.dhcp_srv_ip_addr[0]
              );
              offered_ip <= rx.hdr.dhcp_nxt_cli_addr;
              server_ip  <= rx.hdr.dhcp_srv_ip_addr;
              fsm <= request_s;
            end
          end
        end
        request_s : begin
          timeout <= 0;
          tx.val <= 1;
  
          tx.hdr.dhcp_op           <= dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REQUEST;
          tx.hdr.dhcp_htype        <= 1;
          tx.hdr.dhcp_hlen         <= 6;
          tx.hdr.dhcp_hops         <= 0;
          tx.hdr.dhcp_xid          <= dhcp_xid;
          tx.hdr.dhcp_secs         <= 0; 
          tx.hdr.dhcp_flags        <= 16'h8000;
          tx.hdr.dhcp_cur_cli_addr <= 0; 
          tx.hdr.dhcp_nxt_cli_addr <= 0; 
          tx.hdr.dhcp_srv_ip_addr  <= 0; 
          tx.hdr.dhcp_retrans_addr <= 0; 
          tx.hdr.dhcp_chaddr       <= {MAC_ADDR, {10{8'h00}}};
          tx.hdr.dhcp_sname        <= 0;
          tx.hdr.dhcp_file         <= 0;
          tx.hdr.dhcp_cookie       <= dhcp_vlg_pkg::DHCP_COOKIE;
          
          tx.opt_hdr.dhcp_opt_message_type                      <= dhcp_vlg_pkg::DHCP_MSG_TYPE_REQUEST;
          tx.opt_hdr.dhcp_opt_subnet_mask                       <= 0;
          tx.opt_hdr.dhcp_opt_renewal_time                      <= 0;
          tx.opt_hdr.dhcp_opt_rebinding_time                    <= 0;
          tx.opt_hdr.dhcp_opt_ip_addr_lease_time                <= 0;
          tx.opt_hdr.dhcp_opt_requested_ip_address              <= offered_ip;
          tx.opt_hdr.dhcp_opt_dhcp_server_id                    <= server_ip;
          tx.opt_hdr.dhcp_opt_dhcp_client_id                    <= {1'b1, MAC_ADDR};
          tx.opt_hdr.dhcp_opt_router                            <= 0;
          tx.opt_hdr.dhcp_opt_domain_name_server                <= 0;
          tx.opt_hdr.dhcp_opt_hostname                          <= HOSTNAME;
          tx.opt_hdr.dhcp_opt_domain_name                       <= DOMAIN_NAME;
          tx.opt_hdr.dhcp_opt_fully_qualified_domain_name       <= {{3{8'h00}}, FQDN};
          
          tx.opt_len.dhcp_opt_hostname_len                      <= HOSTNAME_LEN; 
          tx.opt_len.dhcp_opt_domain_name_len                   <= DOMAIN_NAME_LEN; 
          tx.opt_len.dhcp_opt_fully_qualified_domain_name_len   <= FQDN_LEN;
  
          tx.opt_pres.dhcp_opt_message_type_pres                <= 1;
          tx.opt_pres.dhcp_opt_subnet_mask_pres                 <= 0;
          tx.opt_pres.dhcp_opt_renewal_time_pres                <= 0;
          tx.opt_pres.dhcp_opt_rebinding_time_pres              <= 0;
          tx.opt_pres.dhcp_opt_ip_addr_lease_time_pres          <= 0;
          tx.opt_pres.dhcp_opt_requested_ip_address_pres        <= 1;
          tx.opt_pres.dhcp_opt_dhcp_server_id_pres              <= 0;
          tx.opt_pres.dhcp_opt_dhcp_client_id_pres              <= 1;
          tx.opt_pres.dhcp_opt_router_pres                      <= 0;
          tx.opt_pres.dhcp_opt_domain_name_server_pres          <= 0;
          tx.opt_pres.dhcp_opt_hostname_pres                    <= 1;
          tx.opt_pres.dhcp_opt_domain_name_pres                 <= 0;
          tx.opt_pres.dhcp_opt_fully_qualified_domain_name_pres <= 1;
          tx.opt_pres.dhcp_opt_end_pres                         <= 1;
          
          tx.src_ip                                             <= {8'h0, 8'h0, 8'h0, 8'h0};
          tx.dst_ip                                             <= ipv4_vlg_pkg::IPV4_BROADCAST;       
          tx.ipv4_id                                            <= tx.ipv4_id + 1;
          fsm <= ack_s;
          if (VERBOSE) $display("[DUT]-> DHCP request. Requested IP: %d.%d.%d.%d.",
            offered_ip[3],
            offered_ip[2],
            offered_ip[1],
            offered_ip[0]
          );
        end
        ack_s : begin
          tx.val <= 0;
          timeout_ctr <= timeout_ctr + 1;
          if (timeout_ctr == TIMEOUT) timeout <= 1;
          if (rx.val) begin
            if (rx.hdr.dhcp_xid == dhcp_xid &&
              rx.hdr.dhcp_op == dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY &&
              rx.opt_pres.dhcp_opt_message_type_pres &&
              rx.opt_hdr.dhcp_opt_message_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_ACK
            ) begin
              if (VERBOSE) $display("[DUT]<- DHCP acknowledge. Assigned IP: %d.%d.%d.%d.",
                rx.hdr.dhcp_nxt_cli_addr[3],
                rx.hdr.dhcp_nxt_cli_addr[2],
                rx.hdr.dhcp_nxt_cli_addr[1],
                rx.hdr.dhcp_nxt_cli_addr[0]
              );
              ctrl.success <= 1;
              ctrl.assig_ip <= rx.hdr.dhcp_nxt_cli_addr;
              if (rx.opt_pres.dhcp_opt_router_pres) begin
                ctrl.router_ipv4_addr_val <= rx.opt_hdr.dhcp_opt_router;
                ctrl.router_ipv4_addr_val <= 1;
              end
              if (rx.opt_pres.dhcp_opt_subnet_mask_pres) begin
                ctrl.subnet_mask <= rx.opt_hdr.dhcp_opt_subnet_mask;
                ctrl.subnet_mask_val <= 1;
              end
            end
          end
          if (ctrl.success) fsm <= idle_s;
        end
      endcase
    end
  end
  
  always @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= timeout;
  
  assign ctrl.ready = (ctrl.fail || ctrl.success);
  
  always @ (posedge clk) begin
    if (rst) begin
      try_cnt   <= 0;
      ctrl.fail <= 0;
      enable    <= 0;
    end
    else begin
      // Process 'ctrl.ready' signal
      if (ctrl.start && !enable) begin
        try_cnt   <= 0;
        ctrl.fail <= 0;
        enable    <= 1;
      end
      else if (ctrl.ready) begin
        enable <= 0;
      end
      else if (timeout && !fsm_rst) begin // timeout goes high for 2 ticks due to rst delay. Account for that
        try_cnt <= try_cnt + 1;
        if (try_cnt == RETRIES) ctrl.fail <= 1;
      end
    end
  end

endmodule : dhcp_vlg_core
