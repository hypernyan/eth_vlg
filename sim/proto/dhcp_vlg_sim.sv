package sim_dhcp_pkg;
  import ipv4_vlg_pkg::*;
  import udp_vlg_pkg::*;
  import dhcp_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import sim_ipv4_pkg::*;
  import sim_udp_pkg::*;

  localparam ipv4_t SUBNET_MASK = 32'hffffff00; // 255.255.255.0
  
  typedef struct packed {
    mac_addr_t     mac_addr;   // Client's MAC
    mac_addr_t     mac_valid;  // Client's MAC is valid
    ipv4_t         ipv4_addr;  // Client's assigned IPv4. Only valid with ipv4_valid
    bit            ipv4_valid; // Indicate that IPv4 was assigned to this MAC
    bit [3:0][7:0] xid;
  } dhcp_entry_t;

  class dhcp_vlg_sim #(
    parameter int                        DEPTH                = 8,
    parameter bit                        VERBOSE              = 1,
    parameter ipv4_t                     IPV4_ADDRESS         = {8'd192, 8'd168, 8'd0, 8'd1},
    parameter ipv4_t                     ROUTER_IPV4_ADDRESS  = {8'd192, 8'd168, 8'd0, 8'd1},
    parameter mac_addr_t                 MAC_ADDRESS          = 48'hdeadbeef01,
    parameter ipv4_t                     START_IPV4_ADDR_POOL = {8'd192, 8'd168, 8'd0, 8'd100},
    parameter ipv4_t                     STOP_IPV4_ADDR_POOL  = {8'd192, 8'd168, 8'd0, 8'd200},
    parameter [7:0]                      DOMAIN_NAME_LEN      = 5,
    parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME          = "fpga0"
  ) extends device_udp_c;
  
    dhcp_entry_t [2**DEPTH-1:0] dhcp_table;

    function new;
      dhcp_table = 0;
    endfunction : new

    protected task automatic dhcp_parse;
      input  byte            data_in [];
      output dhcp_hdr_t      hdr;
      output dhcp_opt_hdr_t  opt_hdr;
      output dhcp_opt_pres_t opt_pres;
      output dhcp_opt_len_t  opt_len;
      output mac_hdr_t       mac_hdr;
      output ipv4_hdr_t      ipv4_hdr;
      output udp_hdr_t       udp_hdr;
      output bit             ok = 0;

      byte opt_data [];
      dhcp_opt_field_t opt_field, nxt_opt_field;
      dhcp_opt_t cur_opt, nxt_opt;
      byte opt_cnt;
      
      byte data_eth  [];
      byte data_ipv4 [];
      byte data_udp  [];
      byte data_dhcp [];
      
      byte cur_opt_len;
      logic [dhcp_vlg_pkg::OPT_LEN-1:0][7:0] cur_data;
      int len;
      int opt_hdr_len;
      
      bit fcs_ok;
      bit ipv4_ok;
      bit udp_ok;
      bit dhcp_ok;
      
      eth_parse(data_in, data_eth, mac_hdr, fcs_ok);
      if (!fcs_ok) disable dhcp_parse;
      if (mac_hdr.ethertype != IPv4) disable dhcp_parse;

      ipv4_parse(data_eth, data_ipv4, ipv4_hdr, ipv4_ok);
      if (!ipv4_ok) disable dhcp_parse;
      if (ipv4_hdr.proto != UDP) disable dhcp_parse;

      udp_parse(data_ipv4, data_udp, udp_hdr, udp_ok);
      if (!udp_ok) disable dhcp_parse;
      if (udp_hdr.src_port != dhcp_vlg_pkg::DHCP_CLI_PORT || udp_hdr.dst_port != dhcp_vlg_pkg::DHCP_SRV_PORT) disable dhcp_parse;

      opt_field = dhcp_opt_field_kind;
      len = data_udp.size();
      opt_hdr_len = data_udp.size() - dhcp_vlg_pkg::DHCP_HDR_LEN;
      hdr = {>>{data_udp with [0:dhcp_vlg_pkg::DHCP_HDR_LEN-1]}};
      opt_hdr  = 0;
      opt_pres = 0;
      opt_len  = 0;
      for (int i = dhcp_vlg_pkg::DHCP_HDR_LEN; i < len; i = i + 1) begin
        case (opt_field)
          dhcp_opt_field_kind : begin
            case (data_udp[i])
              DHCP_OPT_MSG_TYPE : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_msg_type;
                opt_pres.dhcp_opt_msg_type_pres = 1;
              end
              DHCP_OPT_NET_MASK : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_net_mask;
                opt_pres.dhcp_opt_net_mask_pres = 1;
              end
              DHCP_OPT_RENEW_TIME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_renew_time; 
                opt_pres.dhcp_opt_renew_time_pres = 1; 
              end
              DHCP_OPT_REBIND_TIME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_rebind_time;
                opt_pres.dhcp_opt_rebind_time_pres = 1;
              end
              DHCP_OPT_LEASE_TIME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_lease_time;  
                opt_pres.dhcp_opt_lease_time_pres = 1;  
              end
              DHCP_OPT_REQ_IP : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_req_ip;  
                opt_pres.dhcp_opt_req_ip_pres = 1;  
              end
              DHCP_OPT_DHCP_CLI_ID : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_dhcp_cli_id;
                opt_pres.dhcp_opt_dhcp_cli_id_pres = 1;
              end
              DHCP_OPT_DHCP_SRV_ID : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_dhcp_srv_id;
                opt_pres.dhcp_opt_dhcp_srv_id_pres = 1;
              end
              DHCP_OPT_ROUTER : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_router;
                opt_pres.dhcp_opt_router_pres = 1;
              end
              DHCP_OPT_DNS : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_dns;
                opt_pres.dhcp_opt_dns_pres = 1;
              end
              DHCP_OPT_DOMAIN_NAME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_domain_name;
                opt_pres.dhcp_opt_domain_name_pres = 1;
              end
              DHCP_OPT_FQDN : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_fqdn;
                opt_pres.dhcp_opt_fqdn_pres = 1;               
              end
              DHCP_OPT_HOSTNAME : begin
                nxt_opt_field = dhcp_opt_field_len;
                cur_opt = dhcp_opt_hostname;
                opt_pres.dhcp_opt_hostname_pres = 1;                   
              end
              DHCP_OPT_PAD : begin
                nxt_opt_field = dhcp_opt_field_kind;
                cur_opt = dhcp_opt_pad;
              end
              DHCP_OPT_END : begin
                nxt_opt_field = dhcp_opt_field_kind;
                cur_opt = dhcp_opt_end;
                opt_pres.dhcp_opt_end_pres = 1;
              end
              default : begin
                nxt_opt_field = dhcp_opt_field_len;
              end
            endcase
            opt_cnt = 0;
            cur_data = 0;
            cur_opt_len = 0;
          end
          dhcp_opt_field_len : begin
            cur_opt_len = data_udp[i];
            case (cur_opt)
              dhcp_opt_hostname                    : opt_len.dhcp_opt_hostname_len = cur_opt_len;
              dhcp_opt_domain_name                 : opt_len.dhcp_opt_domain_name_len = cur_opt_len;
              dhcp_opt_fqdn : opt_len.dhcp_opt_fqdn_len = cur_opt_len;
            endcase
            nxt_opt_field =  dhcp_opt_field_data;
          end
          dhcp_opt_field_data : begin
            cur_data[dhcp_vlg_pkg::OPT_LEN-1:0] = {cur_data[dhcp_vlg_pkg::OPT_LEN-2:0], data_udp[i]};
              case (cur_opt)
                dhcp_opt_msg_type                : opt_hdr.dhcp_opt_msg_type                = data_udp[i]; 
                dhcp_opt_net_mask                 : opt_hdr.dhcp_opt_net_mask                 [dhcp_vlg_pkg::DHCP_OPT_NET_MASK_LEN                -opt_cnt-1] = data_udp[i];
                dhcp_opt_renew_time                : opt_hdr.dhcp_opt_renew_time                [dhcp_vlg_pkg::DHCP_OPT_RENEW_TIME_LEN               -opt_cnt-1] = data_udp[i];
                dhcp_opt_rebind_time              : opt_hdr.dhcp_opt_rebind_time              [dhcp_vlg_pkg::DHCP_OPT_REBIND_TIME_LEN             -opt_cnt-1] = data_udp[i];
                dhcp_opt_lease_time          : opt_hdr.dhcp_opt_lease_time          [dhcp_vlg_pkg::DHCP_OPT_LEASE_TIME_LEN         -opt_cnt-1] = data_udp[i];
                dhcp_opt_req_ip        : opt_hdr.dhcp_opt_req_ip        [dhcp_vlg_pkg::DHCP_OPT_REQ_IP_LEN       -opt_cnt-1] = data_udp[i];
                dhcp_opt_dhcp_srv_id              : opt_hdr.dhcp_opt_dhcp_srv_id              [dhcp_vlg_pkg::DHCP_OPT_DHCP_SRV_ID_LEN             -opt_cnt-1] = data_udp[i];
                dhcp_opt_dhcp_cli_id              : opt_hdr.dhcp_opt_dhcp_cli_id              [dhcp_vlg_pkg::DHCP_OPT_DHCP_CLI_ID_LEN             -opt_cnt-1] = data_udp[i];
                dhcp_opt_router                      : opt_hdr.dhcp_opt_router                      [dhcp_vlg_pkg::DHCP_OPT_ROUTER_LEN                     -opt_cnt-1] = data_udp[i];
                dhcp_opt_dns          : opt_hdr.dhcp_opt_dns          [dhcp_vlg_pkg::DHCP_OPT_DNS_LEN         -opt_cnt-1] = data_udp[i];
                dhcp_opt_domain_name                 : opt_hdr.dhcp_opt_domain_name                 [dhcp_vlg_pkg::DHCP_OPT_DOMAIN_NAME_LEN                -opt_cnt-1] = data_udp[i];
                dhcp_opt_fqdn : opt_hdr.dhcp_opt_fqdn [dhcp_vlg_pkg::DHCP_OPT_FQDN_LEN-opt_cnt-1] = data_udp[i];
                dhcp_opt_hostname                    : opt_hdr.dhcp_opt_hostname                    [dhcp_vlg_pkg::DHCP_OPT_HOSTNAME_LEN                   -opt_cnt-1] = data_udp[i];
              endcase
              opt_cnt = opt_cnt + 1;
              if (opt_cnt == cur_opt_len) nxt_opt_field = dhcp_opt_field_kind;
            end
        endcase
        opt_field = nxt_opt_field;
      end
      ok = 1;
      if (VERBOSE) begin
        if (opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_DISCOVER) begin
          if (opt_pres.dhcp_opt_req_ip_pres) $display("[SIM]<- DHCP discover: %d.%d.%d.%d.",   
            opt_hdr.dhcp_opt_req_ip[3],
            opt_hdr.dhcp_opt_req_ip[2],
            opt_hdr.dhcp_opt_req_ip[1],
            opt_hdr.dhcp_opt_req_ip[0]
          );
          else $display("[SIM]<- DHCP discover");
        end
        if (opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_REQUEST) begin
          if (opt_pres.dhcp_opt_req_ip_pres) $display("[SIM]<- DHCP request %d.%d.%d.%d.", 
            opt_hdr.dhcp_opt_req_ip[3],
            opt_hdr.dhcp_opt_req_ip[2],
            opt_hdr.dhcp_opt_req_ip[1],
            opt_hdr.dhcp_opt_req_ip[0]
          );
          else $error("[SIM]<- DHCP request without IP");
        end
      end
    endtask : dhcp_parse
    
    protected task automatic dhcp_gen;
      input dhcp_hdr_t      hdr;
      input dhcp_opt_hdr_t  opt_hdr;
      input dhcp_opt_pres_t opt_pres;
      input dhcp_opt_len_t  opt_len;
      output byte           data[];
      udp_hdr_t  udp_hdr;
      ipv4_hdr_t ipv4_hdr;
      mac_hdr_t  mac_hdr;
      byte       data_ipv4 [];
      byte       data_udp  [];
      byte       data_dhcp [];
      logic [dhcp_vlg_pkg::OPT_NUM-1:0][dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_hdr_proto; // 1 byte for end option
      logic [dhcp_vlg_pkg::OPT_LEN-1:0][7:0] data_opt;
      data_dhcp = new[dhcp_vlg_pkg::DHCP_HDR_LEN];
      data_dhcp = {>>{hdr}};
      opt_hdr_proto = {
        {DHCP_OPT_MSG_TYPE,                     DHCP_OPT_MSG_TYPE_LEN,                        opt_hdr.dhcp_opt_msg_type,                {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_MSG_TYPE_LEN                        ){DHCP_OPT_PAD}}},
        {DHCP_OPT_NET_MASK,                      DHCP_OPT_NET_MASK_LEN,                         opt_hdr.dhcp_opt_net_mask,                 {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_NET_MASK_LEN                         ){DHCP_OPT_PAD}}},
        {DHCP_OPT_RENEW_TIME,                     DHCP_OPT_RENEW_TIME_LEN,                        opt_hdr.dhcp_opt_renew_time,                {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_RENEW_TIME_LEN                        ){DHCP_OPT_PAD}}}, 
        {DHCP_OPT_REBIND_TIME,                   DHCP_OPT_REBIND_TIME_LEN,                      opt_hdr.dhcp_opt_rebind_time,              {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_REBIND_TIME_LEN                      ){DHCP_OPT_PAD}}},                      
        {DHCP_OPT_LEASE_TIME,               DHCP_OPT_LEASE_TIME_LEN,                  opt_hdr.dhcp_opt_lease_time,          {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_LEASE_TIME_LEN                  ){DHCP_OPT_PAD}}},               
        {DHCP_OPT_REQ_IP,             DHCP_OPT_REQ_IP_LEN,                opt_hdr.dhcp_opt_req_ip,        {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_REQ_IP_LEN                ){DHCP_OPT_PAD}}},               
        {DHCP_OPT_DHCP_SRV_ID,                   DHCP_OPT_DHCP_SRV_ID_LEN,                      opt_hdr.dhcp_opt_dhcp_srv_id,              {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_DHCP_SRV_ID_LEN                      ){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DHCP_CLI_ID,                   DHCP_OPT_DHCP_CLI_ID_LEN,                      opt_hdr.dhcp_opt_dhcp_cli_id,              {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_DHCP_CLI_ID_LEN                      ){DHCP_OPT_PAD}}},           
        {DHCP_OPT_HOSTNAME,                         opt_len.dhcp_opt_hostname_len,                    opt_hdr.dhcp_opt_hostname                     },  
        {DHCP_OPT_ROUTER,                           DHCP_OPT_ROUTER_LEN,                              opt_hdr.dhcp_opt_router,                      {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_ROUTER_LEN                              ){DHCP_OPT_PAD}}},    
        {DHCP_OPT_DNS,               DHCP_OPT_DNS_LEN,                  opt_hdr.dhcp_opt_dns,          {(dhcp_vlg_pkg::MAX_OPT_PLD-DHCP_OPT_DNS_LEN                  ){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DOMAIN_NAME,                      opt_len.dhcp_opt_domain_name_len,                 opt_hdr.dhcp_opt_domain_name                  },                  
        {DHCP_OPT_FQDN,      opt_len.dhcp_opt_fqdn_len, opt_hdr.dhcp_opt_fqdn  },   
        {{dhcp_vlg_pkg::OPT_LEN-1{DHCP_OPT_PAD}}, DHCP_OPT_END}
      };
      for (int i = 0; i < dhcp_vlg_pkg::OPT_NUM; i = i + 1) begin
        data_opt = opt_hdr_proto[dhcp_vlg_pkg::OPT_NUM-1-i];
        if (opt_pres[dhcp_vlg_pkg::OPT_NUM-1-i]) begin
          data_dhcp = new[data_dhcp.size()+dhcp_vlg_pkg::OPT_LEN](data_dhcp);
          data_dhcp[data_dhcp.size()-1-:dhcp_vlg_pkg::OPT_LEN] = {>>{data_opt}};
        end
      end
      // Set UDP header
      udp_hdr.src_port = dhcp_vlg_pkg::DHCP_SRV_PORT;
      udp_hdr.dst_port = dhcp_vlg_pkg::DHCP_CLI_PORT;
      udp_hdr.length   = data_dhcp.size() + UDP_HDR_LEN;
      // Set IPv4 to broadcast
      ipv4_hdr.ver    = 4;
      ipv4_hdr.ihl    = 5;
      ipv4_hdr.qos    = 0;
      ipv4_hdr.length = udp_hdr.length + IPV4_HDR_LEN;
      ipv4_hdr.id     = 0; // todo sometahing
      ipv4_hdr.zero   = 0; // 
      ipv4_hdr.df     = 0;
      ipv4_hdr.mf     = 0;
      ipv4_hdr.fo     = 0;
      ipv4_hdr.ttl    = 128;
      ipv4_hdr.proto  = UDP;
      ipv4_hdr.cks    = 0;
      ipv4_hdr.src_ip = IPV4_ADDRESS;
      ipv4_hdr.dst_ip = {4{8'hff}};
      udp_gen(data_dhcp, data_udp, udp_hdr);
      ipv4_gen(data_udp, data_ipv4, ipv4_hdr, MAC_ADDRESS, {6{8'hff}}, mac_hdr);
      eth_gen(data_ipv4, data, mac_hdr);
      if (opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_OFFER) if (VERBOSE) $display("[SIM]-> DHCP offering %d.%d.%d.%d.", 
        hdr.dhcp_nxt_cli_addr[3],
        hdr.dhcp_nxt_cli_addr[2],
        hdr.dhcp_nxt_cli_addr[1],
        hdr.dhcp_nxt_cli_addr[0]
      );
      if (opt_hdr.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_ACK) if (VERBOSE) $display("[SIM]-> DHCP acknowledging %d.%d.%d.%d", 
        hdr.dhcp_nxt_cli_addr[3],
        hdr.dhcp_nxt_cli_addr[2],
        hdr.dhcp_nxt_cli_addr[1],
        hdr.dhcp_nxt_cli_addr[0]
      );
    endtask : dhcp_gen

    protected task automatic pkt_handle;
      input  mac_hdr_t        mac_hdr_in;
      input  dhcp_hdr_t       hdr_in;
      input  dhcp_opt_hdr_t   opt_hdr_in;
      input  dhcp_opt_pres_t  opt_pres_in;
      input  dhcp_opt_len_t   opt_len_in;

      output dhcp_hdr_t       hdr_out;
      output dhcp_opt_hdr_t   opt_hdr_out;
      output dhcp_opt_pres_t  opt_pres_out;
      output dhcp_opt_len_t   opt_len_out;
      output bit              tx_val;
      ipv4_t assigned_ip;
      bit mac_found;
      bit xid_found;
      bit ipv4_found;
      int mac_index;
      int xid_index;
      int ipv4_index;
      bit full;
      bit dhcp_table_full;
      tx_val = 1; // Reply if nothing in this task sets tx_val to 0
    // if (VERBOSE) $display("[SIM] DHCP Server: processing packet from %h:%h:%h:%h:%h:%h.",
    //     mac_hdr_in.src_mac[5],
    //     mac_hdr_in.src_mac[4],
    //     mac_hdr_in.src_mac[3],
    //     mac_hdr_in.src_mac[2],
    //     mac_hdr_in.src_mac[1],
    //     mac_hdr_in.src_mac[0]
    //   );
      // Find MAC entry
      lookup_mac (
        mac_hdr_in.src_mac,
        mac_found,
        mac_index
      );
      lookup_xid (
        hdr_in.dhcp_xid,
        xid_found,
        xid_index
      );
      // Process IP request
      // DHCP discover
      if (opt_pres_in.dhcp_opt_msg_type_pres && opt_hdr_in.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_DISCOVER) begin
        if (opt_pres_in.dhcp_opt_req_ip_pres) begin
          // Find if requested IP is already in table
          lookup_ipv4(opt_hdr_in.dhcp_opt_req_ip, ipv4_found, ipv4_index);
          // Entry containing MAC and IPv4 is already in table
          if (mac_found && ipv4_found && (mac_index == ipv4_index)) begin
            assigned_ip = opt_hdr_in.dhcp_opt_req_ip;
            assign_ip(mac_hdr_in.src_mac, assigned_ip, full, mac_index);          
          end
          // MAC found, but no IP assigned
          else if (mac_found) begin
            gen_free_ipv4(START_IPV4_ADDR_POOL, STOP_IPV4_ADDR_POOL, assigned_ip, dhcp_table_full);
            assign_ip(mac_hdr_in.src_mac, assigned_ip, full, mac_index);
          end
          // No MAC nor IP found
          else if (!mac_found && !ipv4_found) begin
            add_entry(mac_hdr_in.src_mac, hdr_in.dhcp_xid, mac_index, full);
            assign_ip(mac_hdr_in.src_mac, opt_hdr_in.dhcp_opt_req_ip, full, mac_index);
            assigned_ip = opt_hdr_in.dhcp_opt_req_ip;
          end
          // IP assigned for other MAC
          else if (!mac_found && ipv4_found) begin
            add_entry(mac_hdr_in.src_mac, hdr_in.dhcp_xid, mac_index, full);
            gen_free_ipv4 (START_IPV4_ADDR_POOL, STOP_IPV4_ADDR_POOL, assigned_ip, dhcp_table_full);
            assign_ip(mac_hdr_in.src_mac, assigned_ip, full, mac_index);
          end
        end
        else $error("[SIM] DHCP Server: Message Type option missing");
      end
      else if (opt_pres_in.dhcp_opt_msg_type_pres && opt_hdr_in.dhcp_opt_msg_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_REQUEST) begin
        if (mac_found && (xid_index == mac_index)) begin
          lookup_ipv4(opt_hdr_in.dhcp_opt_req_ip, ipv4_found, ipv4_index);
          if (mac_index == ipv4_index) assigned_ip = opt_hdr_in.dhcp_opt_req_ip;
          else begin
            tx_val = 0;
            $error("[SIM] DHCP Server: bad IP request.");
          end 
        end
        else begin
          tx_val = 0;
          $error("[SIM] DHCP Server: DHCP request from unknown MAC %h", mac_hdr_in.src_mac);
        end
      end
    // No IP requested (not used)
    // else begin
    //   gen_free_ipv4 (100, 200, assigned_ip, dhcp_table_full);
    //   assign_ip(mac_hdr_in.src_mac, assigned_ip, full, mac_index);          
    //   ipv4_found = 0;
    // end
      case (opt_hdr_in.dhcp_opt_msg_type)
        dhcp_vlg_pkg::DHCP_MSG_TYPE_DISCOVER : begin
          hdr_out.dhcp_op                                        = dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY;
          hdr_out.dhcp_htype                                     = 1;
          hdr_out.dhcp_hlen                                      = 6;
          hdr_out.dhcp_hops                                      = 0;
          hdr_out.dhcp_xid                                       = hdr_in.dhcp_xid;
          hdr_out.dhcp_secs                                      = 0; 
          hdr_out.dhcp_flags                                     = 16'h8000;
          hdr_out.dhcp_cur_cli_addr                              = 0; 
          hdr_out.dhcp_nxt_cli_addr                              = assigned_ip; 
          hdr_out.dhcp_srv_ip_addr                               = IPV4_ADDRESS; 
          hdr_out.dhcp_retrans_addr                              = 0; 
          hdr_out.dhcp_chaddr                                    = {MAC_ADDRESS, {10{8'h00}}};
          hdr_out.dhcp_sname                                     = 0;
          hdr_out.dhcp_file                                      = 0;
          hdr_out.dhcp_cookie                                    = dhcp_vlg_pkg::DHCP_COOKIE;

          opt_hdr_out.dhcp_opt_msg_type                      = dhcp_vlg_pkg::DHCP_MSG_TYPE_OFFER;
          opt_hdr_out.dhcp_opt_net_mask                       = SUBNET_MASK;
          opt_hdr_out.dhcp_opt_renew_time                      = 43200; // 12hrs
          opt_hdr_out.dhcp_opt_rebind_time                    = 75600; // 21hrs
          opt_hdr_out.dhcp_opt_lease_time                = 86400; // 24hrs
          opt_hdr_out.dhcp_opt_req_ip              = 0;
          opt_hdr_out.dhcp_opt_dhcp_srv_id                    = IPV4_ADDRESS;
          opt_hdr_out.dhcp_opt_dhcp_cli_id                    = 0;
          opt_hdr_out.dhcp_opt_router                            = ROUTER_IPV4_ADDRESS;
          opt_hdr_out.dhcp_opt_dns                = IPV4_ADDRESS;
          opt_hdr_out.dhcp_opt_hostname                          = 0;
          opt_hdr_out.dhcp_opt_domain_name                       = {DOMAIN_NAME, {(dhcp_vlg_pkg::OPT_LEN-DOMAIN_NAME_LEN){DHCP_OPT_PAD}}};
          opt_hdr_out.dhcp_opt_fqdn       = 0;

          opt_len_out.dhcp_opt_hostname_len                      = 0;
          opt_len_out.dhcp_opt_domain_name_len                   = DOMAIN_NAME_LEN; 
          opt_len_out.dhcp_opt_fqdn_len   = 0;

          opt_pres_out.dhcp_opt_msg_type_pres                = 1;
          opt_pres_out.dhcp_opt_net_mask_pres                 = 1;
          opt_pres_out.dhcp_opt_renew_time_pres                = 1;
          opt_pres_out.dhcp_opt_rebind_time_pres              = 1;
          opt_pres_out.dhcp_opt_lease_time_pres          = 1;
          opt_pres_out.dhcp_opt_req_ip_pres        = 0;
          opt_pres_out.dhcp_opt_dhcp_srv_id_pres              = 1;
          opt_pres_out.dhcp_opt_dhcp_cli_id_pres              = 0;
          opt_pres_out.dhcp_opt_router_pres                      = 1;
          opt_pres_out.dhcp_opt_dns_pres          = 1;
          opt_pres_out.dhcp_opt_hostname_pres                    = 0;
          opt_pres_out.dhcp_opt_domain_name_pres                 = 1;
          opt_pres_out.dhcp_opt_fqdn_pres = 0;
          opt_pres_out.dhcp_opt_end_pres                         = 1;
        end
        dhcp_vlg_pkg::DHCP_MSG_TYPE_REQUEST : begin
          hdr_out.dhcp_op                                        = dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY;
          hdr_out.dhcp_htype                                     = 1;
          hdr_out.dhcp_hlen                                      = 6;
          hdr_out.dhcp_hops                                      = 0;
          hdr_out.dhcp_xid                                       = hdr_in.dhcp_xid;
          hdr_out.dhcp_secs                                      = 0; 
          hdr_out.dhcp_flags                                     = 16'h8000;
          hdr_out.dhcp_cur_cli_addr                              = 0; 
          hdr_out.dhcp_nxt_cli_addr                              = assigned_ip; 
          hdr_out.dhcp_srv_ip_addr                               = IPV4_ADDRESS; 
          hdr_out.dhcp_retrans_addr                              = 0; 
          hdr_out.dhcp_chaddr                                    = {MAC_ADDRESS, {10{8'h00}}};
          hdr_out.dhcp_sname                                     = 0;
          hdr_out.dhcp_file                                      = 0;
          hdr_out.dhcp_cookie                                    = dhcp_vlg_pkg::DHCP_COOKIE;

          opt_hdr_out.dhcp_opt_msg_type                      = dhcp_vlg_pkg::DHCP_MSG_TYPE_ACK;
          opt_hdr_out.dhcp_opt_net_mask                       = SUBNET_MASK;
          opt_hdr_out.dhcp_opt_renew_time                      = 43200; // 12hrs
          opt_hdr_out.dhcp_opt_rebind_time                    = 75600; // 21hrs
          opt_hdr_out.dhcp_opt_lease_time                = 86400; // 24hrs
          opt_hdr_out.dhcp_opt_req_ip              = 0;
          opt_hdr_out.dhcp_opt_dhcp_srv_id                    = IPV4_ADDRESS;
          opt_hdr_out.dhcp_opt_dhcp_cli_id                    = 0;
          opt_hdr_out.dhcp_opt_router                            = ROUTER_IPV4_ADDRESS;
          opt_hdr_out.dhcp_opt_dns                = IPV4_ADDRESS;
          opt_hdr_out.dhcp_opt_hostname                          = 0;
          opt_hdr_out.dhcp_opt_domain_name                       = {DOMAIN_NAME, {(dhcp_vlg_pkg::OPT_LEN-DOMAIN_NAME_LEN){DHCP_OPT_PAD}}};
          opt_hdr_out.dhcp_opt_fqdn       = 0;

          opt_len_out.dhcp_opt_hostname_len                      = 0; 
          opt_len_out.dhcp_opt_domain_name_len                   = DOMAIN_NAME_LEN; 
          opt_len_out.dhcp_opt_fqdn_len   = 0;

          opt_pres_out.dhcp_opt_msg_type_pres                = 1;
          opt_pres_out.dhcp_opt_net_mask_pres                 = 1;
          opt_pres_out.dhcp_opt_renew_time_pres                = 1;
          opt_pres_out.dhcp_opt_rebind_time_pres              = 1;
          opt_pres_out.dhcp_opt_lease_time_pres          = 1;
          opt_pres_out.dhcp_opt_req_ip_pres        = 0;
          opt_pres_out.dhcp_opt_dhcp_srv_id_pres              = 1;
          opt_pres_out.dhcp_opt_dhcp_cli_id_pres              = 0;
          opt_pres_out.dhcp_opt_router_pres                      = 1;
          opt_pres_out.dhcp_opt_dns_pres          = 1;
          opt_pres_out.dhcp_opt_hostname_pres                    = 0;
          opt_pres_out.dhcp_opt_domain_name_pres                 = 1;
          opt_pres_out.dhcp_opt_fqdn_pres = 0;
          opt_pres_out.dhcp_opt_end_pres                         = 1;
        end
        default : begin
          $error("[SIM] DHCP Server: unknown message type: %h", opt_hdr_in.dhcp_opt_msg_type);
        end
      endcase
    endtask : pkt_handle

    protected task automatic lookup_ipv4;
      input  ipv4_t ipv4_addr;
      output bit    found;
      output int    index;
      found = 0;
      foreach (dhcp_table[i]) begin
        if (dhcp_table[i].ipv4_valid) begin
          if (dhcp_table[i].ipv4_addr == ipv4_addr) begin
            if (VERBOSE) $display("[SIM] DHCP Server: %d.%d.%d.%d is already assigned to %h:%h:%h:%h:%h:%h.",
              dhcp_table[i].ipv4_addr[3],
              dhcp_table[i].ipv4_addr[2],
              dhcp_table[i].ipv4_addr[1],
              dhcp_table[i].ipv4_addr[0],
              dhcp_table[i].mac_addr[5],
              dhcp_table[i].mac_addr[4],
              dhcp_table[i].mac_addr[3],
              dhcp_table[i].mac_addr[2],
              dhcp_table[i].mac_addr[1],
              dhcp_table[i].mac_addr[0]
            );
            index = i;
            found = 1;
            disable lookup_ipv4;
          end
        end
      end
      if (VERBOSE) $display("[SIM] DHCP Server: %d.%d.%d.%d is free",
        ipv4_addr[3],
        ipv4_addr[2],
        ipv4_addr[1],
        ipv4_addr[0]
      );
    endtask : lookup_ipv4

    protected task automatic lookup_mac;
      input  mac_addr_t   mac_addr;
      output bit          found;
      output int          index;
      found = 0;
      foreach (dhcp_table[i])  begin
        if (dhcp_table[i].mac_valid) begin
          if (dhcp_table[i].mac_addr == mac_addr) begin
            if (VERBOSE) $display("[SIM] DHCP Server: %d.%d.%d.%d is bound to %h:%h:%h:%h:%h:%h",
              dhcp_table[i].ipv4_addr[3],
              dhcp_table[i].ipv4_addr[2],
              dhcp_table[i].ipv4_addr[1],
              dhcp_table[i].ipv4_addr[0],
              dhcp_table[i].mac_addr[5],
              dhcp_table[i].mac_addr[4],
              dhcp_table[i].mac_addr[3],
              dhcp_table[i].mac_addr[2],
              dhcp_table[i].mac_addr[1],
              dhcp_table[i].mac_addr[0]
            );
            index = i;
            found = 1;
            disable lookup_mac;
          end
        end
      end
    //  if (VERBOSE) $display("[SIM] DHCP Server: No entry found for %h:%h:%h:%h:%h:%h.",
    //    mac_addr[5],
    //    mac_addr[4],
    //    mac_addr[3],
    //    mac_addr[2],
    //    mac_addr[1],
    //    mac_addr[0]
    //  );
    endtask : lookup_mac
    
    protected task automatic lookup_xid;
      input bit [3:0][7:0] xid;
      output bit           found;
      output int           index;
      found = 0;
      foreach (dhcp_table[i]) begin
        if (dhcp_table[i].mac_valid) begin
          if (dhcp_table[i].xid == xid) begin
            if (VERBOSE) $display("[SIM] DHCP Server: xid %h bound to %h:%h:%h:%h:%h:%h",
              xid,
              dhcp_table[i].mac_addr[5],
              dhcp_table[i].mac_addr[4],
              dhcp_table[i].mac_addr[3],
              dhcp_table[i].mac_addr[2],
              dhcp_table[i].mac_addr[1],
              dhcp_table[i].mac_addr[0]
            );
            found = 1;
            index = i;
            disable lookup_xid;
          end
        end
      end
    endtask : lookup_xid

    protected task automatic add_entry;
      input mac_addr_t mac_addr;
      input bit [3:0][7:0] xid;
      output bit       full;
      output int       index;
      full = 1;
      foreach (dhcp_table[i]) begin
        if (!dhcp_table[i].mac_valid) begin
          if (VERBOSE) $display("[SIM] DHCP Server: creating entry for %h:%h:%h:%h:%h:%h",
            mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
          dhcp_table[i].mac_valid  = 1;
          dhcp_table[i].ipv4_valid = 0;
          dhcp_table[i].mac_addr   = mac_addr;
          dhcp_table[i].ipv4_addr  = 0;
          dhcp_table[i].xid        = xid;
          index = i;
          full = 0;
          disable add_entry;
        end
      end
      if (VERBOSE) $display("[SIM] DHCP Server: failed to create entry for %h:%h:%h:%h:%h:%h Table full",
        mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
    endtask : add_entry

    protected task automatic assign_ip;
      input mac_addr_t mac_addr;
      input ipv4_t     ipv4_addr;
      output bit       full;
      output int       index;
      full = 1;
      foreach (dhcp_table[i]) begin
        if (mac_addr == dhcp_table[i].mac_addr && dhcp_table[i].mac_valid) begin
          if (VERBOSE) $display("[SIM] DHCP Server: assigning %d.%d.%d.%d to %h:%h:%h:%h:%h:%h",
            ipv4_addr[3], ipv4_addr[2], ipv4_addr[1], ipv4_addr[0], mac_addr[5],
            mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
          dhcp_table[i].ipv4_valid  = 1;
          dhcp_table[i].mac_valid = 1;
          dhcp_table[i].mac_addr  = mac_addr;
          dhcp_table[i].ipv4_addr = ipv4_addr;
          index = i;
          full = 0;
          disable assign_ip;
        end
      end
      if (VERBOSE) $error("[SIM] DHCP Server: failed to create entry for %h:%h:%h:%h:%h:%h at %d.%d.%d.%d.",
        mac_addr[5],
        mac_addr[4],
        mac_addr[3],
        mac_addr[2],
        mac_addr[1],
        mac_addr[0],
        ipv4_addr[3],
        ipv4_addr[2],
        ipv4_addr[1],
        ipv4_addr[0]
      );
    endtask : assign_ip
    
    protected task automatic gen_free_ipv4;
      input  int    start;
      input  int    stop;
      output ipv4_t ipv4;
      output bit    full;
      bit found;
      int index;
      full = 1;
      for (ipv4_t i = start; i < stop + 1; i = i + 1) begin
        ipv4 = i;
        lookup_ipv4(ipv4, found, index);
        if (!found) begin
          $display("[SIM] DHCP Server: generated IP %d.%d.%d.%d.",
            ipv4[3],
            ipv4[2],
            ipv4[1],
            ipv4[0]
          );
          full = 0;
          disable gen_free_ipv4;
        end
      end
    endtask : gen_free_ipv4
    
    task automatic dhcp_proc;
      input  byte data_in [];
      output byte data_out[];
      output bit  ok;
      output bit  transmit;

      byte            data_in [];
      dhcp_hdr_t      hdr_rx, hdr_tx;
      dhcp_opt_hdr_t  opt_hdr_rx,  opt_hdr_tx;
      dhcp_opt_pres_t opt_pres_rx, opt_pres_tx;
      dhcp_opt_len_t  opt_len_rx,  opt_len_tx;
      mac_hdr_t       mac_hdr_rx;
      ipv4_hdr_t      ipv4_hdr_rx;
      udp_hdr_t       udp_hdr_rx;
      bit ok_rx;

      dhcp_parse(
        data_in,
        hdr_rx,
        opt_hdr_rx,
        opt_pres_rx,
        opt_len_rx,
        mac_hdr_rx,
        ipv4_hdr_rx,
        udp_hdr_rx,
        ok_rx
      );

      if (!ok_rx) disable dhcp_proc;
      pkt_handle(
        mac_hdr_rx,
        hdr_rx,
        opt_hdr_rx,
        opt_pres_rx,
        opt_len_rx,
        hdr_tx,
        opt_hdr_tx,
        opt_pres_tx,
        opt_len_tx,
        transmit
      );
      if (transmit) dhcp_gen(
        hdr_tx,
        opt_hdr_tx,
        opt_pres_tx,
        opt_len_tx,
        data_out
      );
    endtask : dhcp_proc

  endclass : dhcp_vlg_sim

endpackage : sim_dhcp_pkg