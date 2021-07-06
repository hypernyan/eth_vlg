module dhcp_vlg_rx
  import 
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*,
    dhcp_vlg_pkg::*;
 (
  input logic clk,
  input logic rst,
  dhcp.out    dhcp,
  udp.in_rx   udp
);

  logic [DHCP_HDR_LEN-1:0][7:0] hdr;
  logic [dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_data;
  logic [$clog2(dhcp_vlg_pkg::OPT_LEN+1)-1:0] opt_cnt;
  
  logic [15:0] byte_cnt;
  logic [7:0] opt_len;
  
  logic fsm_rst, err, done, receiving, opt_en;
  dhcp_opt_t cur_opt;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      receiving <= 0;
      dhcp.err  <= 0;
      byte_cnt  <= 0;
    end
    else begin
      if (udp.strm.sof && (udp.meta.udp_hdr.dst_port == dhcp_vlg_pkg::DHCP_CLI_PORT) && (udp.meta.udp_hdr.src_port == dhcp_vlg_pkg::DHCP_SRV_PORT)) receiving <= 1;
      if (udp.strm.val) byte_cnt <= byte_cnt + 1;
      if (udp.strm.eof) receiving <= 0;
      hdr[DHCP_HDR_LEN-1:1] <= hdr[DHCP_HDR_LEN-2:0];
    end
  end
  
  assign hdr[0] = udp.strm.dat;
  dhcp_opt_field_t opt_field;
  
  always_ff @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= (dhcp.err || done || udp.strm.eof);
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      opt_len       <= 0;
      opt_en        <= 0;
      done          <= 0;
      opt_data      <= 0;
      dhcp.val      <= 0;
      dhcp.opt_pres <= 0;
      dhcp.opt_len  <= 0;
      opt_field     <= dhcp_opt_field_kind;
      cur_opt       <= dhcp_opt_msg_type;
      opt_cnt       <= 0;
    end
    else if (udp.strm.val) begin
      if (byte_cnt == DHCP_HDR_LEN - 1) begin
        dhcp.hdr <= hdr;
        opt_en <= 1; // start analyzing options
        opt_data <= 0;
      end
      if (opt_en) begin
        case (opt_field)
          dhcp_opt_field_kind : begin
            opt_data <= 0;
            case (udp.strm.dat)
              DHCP_OPT_MSG_TYPE : begin
                //$display("msgt option: %d", udp.strm.dat);
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_msg_type;
                dhcp.opt_pres.dhcp_opt_msg_type_pres <= 1;
              end
              DHCP_OPT_NET_MASK : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_net_mask;
                dhcp.opt_pres.dhcp_opt_net_mask_pres <= 1;
              end
              DHCP_OPT_RENEW_TIME : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_renew_time; 
                dhcp.opt_pres.dhcp_opt_renew_time_pres <= 1;
              end
              DHCP_OPT_REBIND_TIME : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_rebind_time;
                dhcp.opt_pres.dhcp_opt_rebind_time_pres <= 1;
              end
              DHCP_OPT_LEASE_TIME : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_lease_time;  
                dhcp.opt_pres.dhcp_opt_lease_time_pres <= 1;
              end
              DHCP_OPT_REQ_IP : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_req_ip;  
                dhcp.opt_pres.dhcp_opt_req_ip_pres <= 1;             
              end
              DHCP_OPT_DHCP_CLI_ID : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_dhcp_cli_id;
                dhcp.opt_pres.dhcp_opt_dhcp_cli_id_pres <= 1;
              end
              DHCP_OPT_DHCP_SRV_ID : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_dhcp_srv_id;
                dhcp.opt_pres.dhcp_opt_dhcp_srv_id_pres <= 1;
              end
              DHCP_OPT_ROUTER : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_router;
                dhcp.opt_pres.dhcp_opt_router_pres <= 1;
              end
              DHCP_OPT_DNS : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_dns;
                dhcp.opt_pres.dhcp_opt_dns_pres <= 1;
              end
              DHCP_OPT_DOMAIN_NAME : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_domain_name;
                dhcp.opt_pres.dhcp_opt_domain_name_pres <= 1;
              end
              dhcp_opt_fqdn : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_fqdn;
                dhcp.opt_pres.dhcp_opt_fqdn_pres <= 1;
              end
              DHCP_OPT_HOSTNAME : begin
                opt_field <= dhcp_opt_field_len;
                cur_opt <= dhcp_opt_hostname;
                dhcp.opt_pres.dhcp_opt_hostname_pres <= 1;
              end                   
              DHCP_OPT_PAD : begin
                opt_field <= dhcp_opt_field_kind;
                cur_opt <= dhcp_opt_pad;
              end
              DHCP_OPT_END : begin
                dhcp.val <= 1;
                done <= 1;
                opt_field <= dhcp_opt_field_kind;
                cur_opt <= dhcp_opt_end;
              end
              default : begin
                opt_field <= dhcp_opt_field_len;
              end
            endcase
            opt_cnt <= 0;
          end
          dhcp_opt_field_len : begin
            case (cur_opt)
              dhcp_opt_hostname    : dhcp.opt_len.dhcp_opt_hostname_len    <= udp.strm.dat; 
              dhcp_opt_domain_name : dhcp.opt_len.dhcp_opt_domain_name_len <= udp.strm.dat; 
              dhcp_opt_fqdn        : dhcp.opt_len.dhcp_opt_fqdn_len        <= udp.strm.dat;
              default:;
            endcase
            opt_len <= udp.strm.dat;
            opt_field <= (udp.strm.dat == 0) ? dhcp_opt_field_kind : dhcp_opt_field_data;
          end
          dhcp_opt_field_data : begin
             opt_data[0] <= udp.strm.dat;
             opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:1] <= opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-2:0];
            if (opt_cnt == opt_len-1) begin
              opt_field <= dhcp_opt_field_kind;
              case (cur_opt) 
                dhcp_opt_msg_type    : dhcp.opt_hdr.dhcp_opt_msg_type    <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_net_mask    : dhcp.opt_hdr.dhcp_opt_net_mask    <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_renew_time  : dhcp.opt_hdr.dhcp_opt_renew_time  <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_rebind_time : dhcp.opt_hdr.dhcp_opt_rebind_time <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_lease_time  : dhcp.opt_hdr.dhcp_opt_lease_time  <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_req_ip      : dhcp.opt_hdr.dhcp_opt_req_ip      <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_dhcp_srv_id : dhcp.opt_hdr.dhcp_opt_dhcp_srv_id <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_dhcp_cli_id : dhcp.opt_hdr.dhcp_opt_dhcp_cli_id <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_hostname    : dhcp.opt_hdr.dhcp_opt_hostname    <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_router      : dhcp.opt_hdr.dhcp_opt_router      <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_dns         : dhcp.opt_hdr.dhcp_opt_dns         <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_domain_name : dhcp.opt_hdr.dhcp_opt_domain_name <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                dhcp_opt_fqdn        : dhcp.opt_hdr.dhcp_opt_fqdn        <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PLD-1:0], udp.strm.dat};
                default:;
              endcase
            end
            opt_cnt <= opt_cnt + 1;
          end
        endcase
      end
    end
  end

endmodule : dhcp_vlg_rx
