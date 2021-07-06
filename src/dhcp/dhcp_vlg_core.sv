module dhcp_vlg_core
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*,
    dhcp_vlg_pkg::*;
 #(
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
  parameter bit                        VERBOSE         = 1,
  parameter string                     DUT_STRING      = ""

)
(
  input  logic  clk,
  input  logic  rst,

  dhcp_ctl.in   ctl,
  dhcp.in       rx,
  dhcp.out      tx
);

  logic fsm_rst;
  
  enum logic [4:0] {idle_s, discover_s, offer_s, request_s, ack_s} fsm;
  
  ipv4_t offered_ip;
  ipv4_t server_ip; 
  logic timeout, enable;
  
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
  
  logic tmr, tmr_rst, tmr_en;

  eth_vlg_tmr #(
    .TICKS (TIMEOUT),
    .AUTORESET (1))
  tmr_inst (  
    .clk (clk),
    .rst (rst),
    .en  (tmr_en),
    .tmr_rst (1'b0),
    .tmr (timeout)
  );

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm                      <= idle_s;
      tx.val                   <= 0;
      tmr_en                   <= 0;
      ctl.assig_ip             <= 0;
      ctl.router_ipv4_addr_val <= 0;
      ctl.subnet_mask_val      <= 0;
      ctl.router_ipv4_addr_val <= 0;
      ctl.success              <= 0;
      ctl.subnet_mask          <= 0;
      tx.ipv4_id               <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (enable) begin
            fsm <= discover_s;
            tmr_en <= 1;
          end
          else tmr_en <= 0;
        end
        discover_s : begin
          dhcp_xid                 <= xid_prng;
          ctl.success              <= 0;
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
          
          tx.opt_hdr.dhcp_opt_msg_type    <= dhcp_vlg_pkg::DHCP_MSG_TYPE_DISCOVER;
          tx.opt_hdr.dhcp_opt_net_mask    <= 0;
          tx.opt_hdr.dhcp_opt_renew_time  <= 0;
          tx.opt_hdr.dhcp_opt_rebind_time <= 0;
          tx.opt_hdr.dhcp_opt_lease_time  <= 0;
          tx.opt_hdr.dhcp_opt_req_ip      <= ctl.pref_ip;
          tx.opt_hdr.dhcp_opt_dhcp_srv_id <= 0;
          tx.opt_hdr.dhcp_opt_dhcp_cli_id <= {1'b1, MAC_ADDR};
          tx.opt_hdr.dhcp_opt_router      <= 0;
          tx.opt_hdr.dhcp_opt_dns         <= 0;
          tx.opt_hdr.dhcp_opt_hostname    <= HOSTNAME;
          tx.opt_hdr.dhcp_opt_domain_name <= DOMAIN_NAME;
          tx.opt_hdr.dhcp_opt_fqdn.fqdn_flags  <= 8'b00000010; // ascii, server performs update
          tx.opt_hdr.dhcp_opt_fqdn.fqdn_rcode1 <= 0;
          tx.opt_hdr.dhcp_opt_fqdn.fqdn_rcode2 <= 0;
          tx.opt_hdr.dhcp_opt_fqdn.fqdn_str    <= FQDN;
          
          tx.opt_len.dhcp_opt_hostname_len    <= HOSTNAME_LEN; 
          tx.opt_len.dhcp_opt_domain_name_len <= DOMAIN_NAME_LEN; 
          tx.opt_len.dhcp_opt_fqdn_len        <= FQDN_LEN + 3; // 3 bytes before string
  
          tx.opt_pres.dhcp_opt_msg_type_pres    <= 1;
          tx.opt_pres.dhcp_opt_net_mask_pres    <= 0;
          tx.opt_pres.dhcp_opt_renew_time_pres  <= 0;
          tx.opt_pres.dhcp_opt_rebind_time_pres <= 0;
          tx.opt_pres.dhcp_opt_lease_time_pres  <= 0;
          tx.opt_pres.dhcp_opt_req_ip_pres      <= 1;
          tx.opt_pres.dhcp_opt_dhcp_srv_id_pres <= 0;
          tx.opt_pres.dhcp_opt_dhcp_cli_id_pres <= 1;
          tx.opt_pres.dhcp_opt_router_pres      <= 0;
          tx.opt_pres.dhcp_opt_dns_pres         <= 0;
          tx.opt_pres.dhcp_opt_hostname_pres    <= 1;
          tx.opt_pres.dhcp_opt_domain_name_pres <= 0;
          tx.opt_pres.dhcp_opt_fqdn_pres        <= 1;
          tx.opt_pres.dhcp_opt_end_pres         <= 1;
          
          tx.src_ip  <= {8'h0,  8'h0,  8'h0,  8'h0};
          tx.dst_ip  <= ipv4_vlg_pkg::IPV4_BROADCAST;
          tx.ipv4_id <= ipv4_id;
          fsm <= offer_s;
          if (VERBOSE) $display("[", DUT_STRING, "]-> DHCP discover %h. Preferred IP: %d.%d.%d.%d", 
            xid_prng,
            ctl.pref_ip[3], 
            ctl.pref_ip[2],
            ctl.pref_ip[1],
            ctl.pref_ip[0]
          );
        end
        offer_s : begin
          tx.val <= 0;
          if (rx.val) begin
            if (rx.hdr.dhcp_xid == dhcp_xid &&
                rx.hdr.dhcp_op == dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY &&
                rx.opt_pres.dhcp_opt_msg_type_pres &&
                rx.opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_OFFER
            ) begin
              if (VERBOSE) $display("[", DUT_STRING, "]<- DHCP offer %h. Offered IP: %d.%d.%d.%d, Server IP: %d.%d.%d.%d.",
                tx.hdr.dhcp_xid,
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
          
          tx.opt_hdr.dhcp_opt_msg_type         <= dhcp_vlg_pkg::DHCP_MSG_TYPE_REQUEST;
          tx.opt_hdr.dhcp_opt_net_mask         <= 0;
          tx.opt_hdr.dhcp_opt_renew_time       <= 0;
          tx.opt_hdr.dhcp_opt_rebind_time      <= 0;
          tx.opt_hdr.dhcp_opt_lease_time       <= 0;
          tx.opt_hdr.dhcp_opt_req_ip           <= offered_ip;
          tx.opt_hdr.dhcp_opt_dhcp_srv_id      <= server_ip;
          tx.opt_hdr.dhcp_opt_dhcp_cli_id      <= {1'b1, MAC_ADDR};
          tx.opt_hdr.dhcp_opt_router           <= 0;
          tx.opt_hdr.dhcp_opt_dns              <= 0;
          tx.opt_hdr.dhcp_opt_hostname         <= HOSTNAME;
          tx.opt_hdr.dhcp_opt_domain_name      <= DOMAIN_NAME;
          tx.opt_hdr.dhcp_opt_fqdn.fqdn_flags  <= 8'b00000010; // ascii, server performs update
          tx.opt_hdr.dhcp_opt_fqdn.fqdn_rcode1 <= 0;
          tx.opt_hdr.dhcp_opt_fqdn.fqdn_rcode2 <= 0;
          tx.opt_hdr.dhcp_opt_fqdn.fqdn_str    <= FQDN;
          
          tx.opt_len.dhcp_opt_hostname_len     <= HOSTNAME_LEN;
          tx.opt_len.dhcp_opt_domain_name_len  <= DOMAIN_NAME_LEN;
          tx.opt_len.dhcp_opt_fqdn_len         <= FQDN_LEN + 3; // 3 bytes before string
  
          tx.opt_pres.dhcp_opt_msg_type_pres    <= 1;
          tx.opt_pres.dhcp_opt_net_mask_pres    <= 0;
          tx.opt_pres.dhcp_opt_renew_time_pres  <= 0;
          tx.opt_pres.dhcp_opt_rebind_time_pres <= 0;
          tx.opt_pres.dhcp_opt_lease_time_pres  <= 0;
          tx.opt_pres.dhcp_opt_req_ip_pres      <= 1;
          tx.opt_pres.dhcp_opt_dhcp_srv_id_pres <= 0;
          tx.opt_pres.dhcp_opt_dhcp_cli_id_pres <= 1;
          tx.opt_pres.dhcp_opt_router_pres      <= 0;
          tx.opt_pres.dhcp_opt_dns_pres         <= 0;
          tx.opt_pres.dhcp_opt_hostname_pres    <= 1;
          tx.opt_pres.dhcp_opt_domain_name_pres <= 0;
          tx.opt_pres.dhcp_opt_fqdn_pres        <= 1;
          tx.opt_pres.dhcp_opt_end_pres         <= 1;
          
          tx.src_ip  <= {8'h0, 8'h0, 8'h0, 8'h0};
          tx.dst_ip  <= ipv4_vlg_pkg::IPV4_BROADCAST;       
          tx.ipv4_id <= tx.ipv4_id + 1;
          fsm <= ack_s;
          if (VERBOSE) $display("[", DUT_STRING, "]-> DHCP request %h. Requested IP: %d.%d.%d.%d.",
            dhcp_xid,
            offered_ip[3],
            offered_ip[2],
            offered_ip[1],
            offered_ip[0]
          );
        end
        ack_s : begin
          tx.val <= 0;
          if (rx.val) begin
            if (rx.hdr.dhcp_xid == dhcp_xid &&
              rx.hdr.dhcp_op == dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY &&
              rx.opt_pres.dhcp_opt_msg_type_pres &&
              rx.opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_ACK
            ) begin
              if (VERBOSE) $display("[", DUT_STRING, "]<- DHCP acknowledge %h. Assigned IP: %d.%d.%d.%d.",
                rx.hdr.dhcp_xid,
                rx.hdr.dhcp_nxt_cli_addr[3],
                rx.hdr.dhcp_nxt_cli_addr[2],
                rx.hdr.dhcp_nxt_cli_addr[1],
                rx.hdr.dhcp_nxt_cli_addr[0]
              );
              ctl.success  <= 1;
              ctl.assig_ip <= rx.hdr.dhcp_nxt_cli_addr;
              if (rx.opt_pres.dhcp_opt_router_pres) begin
                ctl.router_ipv4_addr_val <= rx.opt_hdr.dhcp_opt_router;
                ctl.router_ipv4_addr_val <= 1;
              end
              if (rx.opt_pres.dhcp_opt_net_mask_pres) begin
                ctl.subnet_mask     <= rx.opt_hdr.dhcp_opt_net_mask;
                ctl.subnet_mask_val <= 1;
              end
            end
          end
          if (ctl.success) fsm <= idle_s;
        end
      endcase
    end
  end
  
  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= timeout;
  
  assign ctl.ready = (ctl.fail || ctl.success);
  
  always_ff @ (posedge clk) begin
    if (rst) begin
      try_cnt   <= 0;
      ctl.fail <= 0;
      enable    <= 0;
    end
    else begin
      // Process 'ctl.ready' signal
      if (ctl.start && !enable) begin // hold enable until ready goes high
        try_cnt  <= 0;
        ctl.fail <= 0;
        enable   <= 1;
      end
      else if (ctl.ready) begin
        enable <= 0;
      end
      // If timeout goes high -> increment try counter
      else if (timeout && !fsm_rst) begin // timeout goes high for 2 ticks due to rst delay. Account for that with !fsm_rst
        try_cnt <= try_cnt + 1;
        if (try_cnt == RETRIES) ctl.fail <= 1;
      end
    end
  end

endmodule : dhcp_vlg_core
