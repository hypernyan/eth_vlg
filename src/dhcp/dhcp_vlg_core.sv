module dhcp_vlg_core
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*,
    dhcp_vlg_pkg::*;
 #(
  parameter mac_addr_t                 MAC_ADDR          = 0,
  parameter [7:0]                      HOSTNAME_LEN      = 0,
  parameter [7:0]                      DOMAIN_NAME_LEN   = 0,
  parameter [7:0]                      FQDN_LEN          = 0,
  parameter [DOMAIN_NAME_LEN-1:0][7:0] DOMAIN_NAME       = "",
  parameter [HOSTNAME_LEN-1:0]   [7:0] HOSTNAME          = "",
  parameter [FQDN_LEN-1:0]       [7:0] FQDN              = "",
  parameter int                        REFCLK_HZ         = 125000000,
  parameter int                        TIMEOUT_SEC       = 10,
  parameter int                        DEFAULT_LEASE_SEC = 600,
  parameter bit                        ENABLE            = 1,
  parameter int                        RETRIES           = 3,
  parameter bit                        VERBOSE           = 1,
  parameter string                     DUT_STRING        = ""

)
(
  input  logic  clk,
  input  logic  rst,

  dhcp_ctl_ifc.in ctl,
  dhcp_ifc.in     rx,
  dhcp_ifc.out    tx,
  input  logic    cts,
  output logic    txe // indication that UDP tx will be used
);
  
  enum logic [7:0] {
    idle_s,     // no IP lease, idling
    wait_s,     // wait for UDP become ready, i.e. finished user tx
    discover_s, // send DHCPDISCOVER
    offer_s,    // wait for DHCPOFFER
    request_s,  // send DHCPREQUEST
    ack_s,      // wait DHCPACK
    upd_s,
    lease_s
  } fsm;
  
  ipv4_t offered_ip;
  ipv4_t server_ip; 
  logic init_timeout, enable;

  logic [31:0] renew_sec;
  logic        renew_pres;
  logic [31:0] rebind_sec;
  logic        rebind_pres;
  logic [31:0] lease_sec;
  logic        lease_pres;
  logic        init_fail;
  logic        renew;
  logic        rebind;
  logic        fsm_rst;
  logic        tick;
  logic        lease_expired;
  logic        init;

  // a bogus situation is possible when DHCP receives an ACK
  // even though the actual REQUEST for that ACK has not been sent
  // this should not nomally occur, but if this happens
  // 'txe' signal will go low as the FSM assumes lease is granted
  // this will cause the subsequent UDP transmission logic to switch to user output
  // while still trying 
  logic        done;

  logic [31:0] lease_tmr;
  
  logic [$clog2(RETRIES+1)-1:0] fail_cnt;
  logic [$clog2(TIMEOUT_SEC+1)-1:0] tmr;
  
  logic [31:0] xid_prng, dhcp_xid;

  ipv4_vlg_pkg::id_t ipv4_id;

  prng prng_dhcp_xid_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (xid_prng)
  );
  
  prng #(.W (16), .POLY (16'hface)) prng_ipv4_id_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (ipv4_id)
  );
  
  logic tick_sec;
  logic lease_renewed;

  eth_vlg_tmr #(
    .TICKS (REFCLK_HZ),
    .AUTORESET (1))
  sec_tmr_inst (  
    .clk     (clk),
    .rst     (rst),
    .en      (1'b1),
    .tmr_rst (1'b0),
    .tmr     (tick) // if timeout counts till timeout
  );

  
  always_ff @ (posedge clk) begin
    if (lease_renewed) begin
      lease_tmr <= 0;
    end
    else if (ctl.lease && tick) lease_tmr <= lease_tmr + 1;
  end
  
  always_ff @ (posedge clk) begin
    if (fsm_rst || lease_renewed) begin
      renew         <= 0;
      rebind        <= 0;
      lease_expired <= 0;
    end
    else if (ctl.lease) begin
      if (lease_tmr == renew_sec)  renew <= 1;
      if (lease_tmr == rebind_sec) rebind <= 1;
      if (lease_tmr == lease_sec)  lease_expired <= 1;
    end
  end

  always_ff @ (posedge clk) fsm_rst <= (init_fail || rst || lease_expired || (fail_cnt == RETRIES));
  
  always_ff @ (posedge clk) begin
    if (rst || ctl.start) begin
      ctl.ready <= 0;
    end
    else if (ctl.lease || (fail_cnt == RETRIES)) begin
      ctl.ready <= 1;
    end
  end

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm                      <= idle_s;
      tx.val                   <= 0;
      tx.ipv4_id               <= 0;
      init_fail                <= 0;
      // don't reset IP for TCP to finish disconnecting
      // in case of DHCP lease expiry
      // ctl.assig_ip             <= 0;
      ctl.router_ipv4_addr_val <= 0;
      ctl.subnet_mask_val      <= 0;
      ctl.router_ipv4_addr_val <= 0;
      ctl.lease                <= 0;
      ctl.subnet_mask          <= 0;
      fail_cnt                 <= 0;
      init                     <= 0;
      lease_renewed            <= 0;
      txe                      <= 0;
      done                     <= 0;
    end
    else begin
      // constant fields
      tx.hdr.dhcp_htype        <= 1;
      tx.hdr.dhcp_hlen         <= 6;
      tx.hdr.dhcp_hops         <= 0;
      tx.hdr.dhcp_retrans_addr <= 0; 
      tx.hdr.dhcp_chaddr       <= {MAC_ADDR, {10{8'h00}}};
      tx.hdr.dhcp_secs         <= 0; 
      tx.hdr.dhcp_flags        <= 16'h8000;
      tx.hdr.dhcp_srv_ip_addr  <= 0; 
      
      tx.opt_hdr.dhcp_opt_net_mask         <= 0;
      tx.opt_hdr.dhcp_opt_renew_time       <= 0;
      tx.opt_hdr.dhcp_opt_rebind_time      <= 0;
      tx.opt_hdr.dhcp_opt_lease_time       <= 0;

      tx.opt_pres.dhcp_opt_msg_type_pres    <= 1;
      tx.opt_pres.dhcp_opt_renew_time_pres  <= 0;
      tx.opt_pres.dhcp_opt_rebind_time_pres <= 0;
      tx.opt_pres.dhcp_opt_lease_time_pres  <= 0;
      tx.opt_hdr.dhcp_opt_dhcp_srv_id       <= 0;
      tx.opt_hdr.dhcp_opt_dhcp_cli_id       <= {1'b1, MAC_ADDR}; // set client id as MAC
      tx.opt_hdr.dhcp_opt_router            <= 0;
      tx.opt_hdr.dhcp_opt_dns               <= 0;
      tx.opt_hdr.dhcp_opt_hostname          <= HOSTNAME;
      tx.opt_hdr.dhcp_opt_domain_name       <= DOMAIN_NAME;
      tx.opt_hdr.dhcp_opt_fqdn.fqdn_flags   <= 8'b00000010; // ascii, server performs update
      tx.opt_hdr.dhcp_opt_fqdn.fqdn_rcode1  <= 0;
      tx.opt_hdr.dhcp_opt_fqdn.fqdn_rcode2  <= 0;
      tx.opt_hdr.dhcp_opt_fqdn.fqdn_str     <= FQDN;

      tx.opt_len.dhcp_opt_hostname_len      <= HOSTNAME_LEN; 
      tx.opt_len.dhcp_opt_domain_name_len   <= DOMAIN_NAME_LEN; 
      tx.opt_len.dhcp_opt_fqdn_len          <= FQDN_LEN + 3; // 3 bytes before string

      tx.src_ip <= {8'h0,  8'h0,  8'h0,  8'h0};
      tx.dst_ip <= ipv4_vlg_pkg::IPV4_BROADCAST;

      tx.opt_pres.dhcp_opt_net_mask_pres    <= 0;
      tx.opt_pres.dhcp_opt_req_ip_pres      <= 1;
      tx.opt_pres.dhcp_opt_dhcp_srv_id_pres <= 0;
      tx.opt_pres.dhcp_opt_dhcp_cli_id_pres <= 1;
      tx.opt_pres.dhcp_opt_router_pres      <= 0;
      tx.opt_pres.dhcp_opt_dns_pres         <= 0;
      tx.opt_pres.dhcp_opt_hostname_pres    <= 1;
      tx.opt_pres.dhcp_opt_domain_name_pres <= 0;
      tx.opt_pres.dhcp_opt_fqdn_pres        <= 1;
      tx.opt_pres.dhcp_opt_end_pres         <= 1;
      // state machine
      case (fsm)
        idle_s : begin
          if (ctl.start || ctl.lease || init) begin
            fsm <= wait_s;
            init <= 1;
          end
          tmr <= 0;
          txe <= 0;
        end
        wait_s : begin
          done <= 0;
          if (cts) begin // wait for UDP's cts
            txe <= 1;
            fsm <= (renew && !rebind) ? request_s : discover_s;
          end
        end
        discover_s : begin
          dhcp_xid  <= xid_prng;
          tx.hdr.dhcp_op           <= dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REQUEST;
          tx.hdr.dhcp_xid          <= (rebind) ? dhcp_xid : xid_prng;
          tx.hdr.dhcp_cur_cli_addr <= 0; 
          tx.hdr.dhcp_nxt_cli_addr <= 0; 
          tx.hdr.dhcp_srv_ip_addr  <= 0; 

          tx.opt_hdr.dhcp_opt_msg_type <= dhcp_vlg_pkg::DHCP_MSG_TYPE_DISCOVER;
          tx.opt_hdr.dhcp_opt_req_ip   <= (rebind) ? ctl.assig_ip : ctl.pref_ip; // if rebinding, use assigned ip, otherwise preffered

          tx.ipv4_id <= ipv4_id;
          tx.val <= 1;

          fsm <= offer_s;
          if (VERBOSE) begin
            if (rebind) $display("[", DUT_STRING, "]-> DHCP discover %h. Attempting to rebind. Requesting IP: %d.%d.%d.%d", 
            xid_prng, ctl.assig_ip[3], ctl.assig_ip[2], ctl.assig_ip[1], ctl.assig_ip[0]);
            else if (!ctl.lease) $display("[", DUT_STRING, "]-> DHCP discover %h. Try %d. Requesting IP: %d.%d.%d.%d", 
            xid_prng, fail_cnt + 1, ctl.pref_ip[3], ctl.pref_ip[2], ctl.pref_ip[1], ctl.pref_ip[0]);
          end
        end
        offer_s : begin
          tx.val <= 0;
          if (tick) tmr <= tmr + 1;
          if (tmr == TIMEOUT_SEC) begin
            fsm <= idle_s;
            if (!renew) fail_cnt <= fail_cnt + 1;
          end
          else if (rx.val) begin
            if (rx.hdr.dhcp_xid == dhcp_xid &&
                rx.hdr.dhcp_op == dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY &&
                rx.opt_pres.dhcp_opt_msg_type_pres &&
                rx.opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_OFFER
            ) begin
              if (VERBOSE) $display("[", DUT_STRING, "]<- DHCP offer %h. Offered IP: %d.%d.%d.%d, Server IP: %d.%d.%d.%d.",
                tx.hdr.dhcp_xid,
                rx.hdr.dhcp_nxt_cli_addr[3], rx.hdr.dhcp_nxt_cli_addr[2], rx.hdr.dhcp_nxt_cli_addr[1], rx.hdr.dhcp_nxt_cli_addr[0],
                rx.hdr.dhcp_srv_ip_addr[3],  rx.hdr.dhcp_srv_ip_addr[2],  rx.hdr.dhcp_srv_ip_addr[1],  rx.hdr.dhcp_srv_ip_addr[0]);
              offered_ip <= rx.hdr.dhcp_nxt_cli_addr;
              server_ip  <= rx.hdr.dhcp_srv_ip_addr;
              fsm <= request_s;
            end
          end
        end
        request_s : begin
          tmr <= 0;
          // Header
          tx.hdr.dhcp_op           <= dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REQUEST;
          tx.hdr.dhcp_xid          <= dhcp_xid;
          tx.hdr.dhcp_cur_cli_addr <= offered_ip; 
          tx.hdr.dhcp_nxt_cli_addr <= 0;
          tx.hdr.dhcp_srv_ip_addr  <= server_ip; 
          // Options
          tx.opt_hdr.dhcp_opt_msg_type  <= dhcp_vlg_pkg::DHCP_MSG_TYPE_REQUEST;
          tx.opt_hdr.dhcp_opt_req_ip    <= offered_ip;

          tx.ipv4_id <= tx.ipv4_id + 1;
          tx.val <= 1;
          fsm <= ack_s;
          if (VERBOSE) begin
            if (renew) $display("[", DUT_STRING, "]-> DHCP request %h. Attempting to renew. Requesting IP: %d.%d.%d.%d", 
            xid_prng, ctl.assig_ip[3], ctl.assig_ip[2], ctl.assig_ip[1], ctl.assig_ip[0]);
            else $display("[", DUT_STRING, "]-> DHCP request %h. Try %d. Requesting IP: %d.%d.%d.%d", 
            xid_prng, fail_cnt + 1, ctl.assig_ip[3], ctl.assig_ip[2], ctl.assig_ip[1], ctl.assig_ip[0]);
          end
        end
        ack_s : begin
          if (tx.done) done <= 1;
          tx.val <= 0;
          if (tick) tmr <= tmr + 1;
          if (tmr == TIMEOUT_SEC) begin
            fsm <= idle_s;
            if (!renew) fail_cnt <= fail_cnt + 1;
          end
          else if (done && rx.val) begin // check that transmission is complete for DHCP
            if (rx.hdr.dhcp_xid == dhcp_xid &&
              rx.hdr.dhcp_op == dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY &&
              rx.opt_pres.dhcp_opt_msg_type_pres ) begin
                if (rx.opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_ACK)  begin
                  fsm <= upd_s;
                  ctl.assig_ip <= rx.hdr.dhcp_nxt_cli_addr;
                  lease_renewed <= 1;
                  if (VERBOSE) $display("[", DUT_STRING, "]<- DHCP acknowledge %h. Assigned IP: %d.%d.%d.%d.",
                    rx.hdr.dhcp_xid,
                    rx.hdr.dhcp_nxt_cli_addr[3], rx.hdr.dhcp_nxt_cli_addr[2], rx.hdr.dhcp_nxt_cli_addr[1], rx.hdr.dhcp_nxt_cli_addr[0]);
                  if (rx.opt_pres.dhcp_opt_router_pres) begin
                    ctl.router_ipv4_addr_val <= rx.opt_hdr.dhcp_opt_router;
                    ctl.router_ipv4_addr_val <= 1;
                  end
                  if (rx.opt_pres.dhcp_opt_net_mask_pres) begin
                    ctl.subnet_mask     <= rx.opt_hdr.dhcp_opt_net_mask;
                    ctl.subnet_mask_val <= 1;
                  end
                  lease_pres  <= rx.opt_pres.dhcp_opt_lease_time_pres;
                  lease_sec   <= (rx.opt_pres.dhcp_opt_lease_time_pres) ? rx.opt_hdr.dhcp_opt_lease_time : DEFAULT_LEASE_SEC;
                  renew_pres  <= rx.opt_pres.dhcp_opt_renew_time_pres;
                  renew_sec   <= rx.opt_hdr.dhcp_opt_renew_time;
                  rebind_pres <= rx.opt_pres.dhcp_opt_rebind_time_pres;
                  rebind_sec  <= rx.opt_hdr.dhcp_opt_rebind_time;
                end
                //if (rx.opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_NAK) begin
                //  fsm <= idle_s;
                //  init_fail <= 1;
                //end Not needed: 'tmr' will expire anyway
            end
          end
        end
        upd_s : begin
          renew_sec  <= (renew_pres)  ? renew_sec  : lease_sec >> 1;
          rebind_sec <= (rebind_pres) ? rebind_sec : lease_sec - (lease_sec >> 3);
          lease_renewed <= 0;
          done <= 0;
          fsm <= lease_s;
        end
        lease_s : begin
          ctl.lease <= 1;
          init <= 0;
          txe <= 0;
          if (renew || rebind) fsm <= wait_s;
        end
        default :;
      endcase
    end
  end

endmodule : dhcp_vlg_core
