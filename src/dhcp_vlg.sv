import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface dhcp (
  dhcp_hdr_t     hdr;
  dhcp_opt_hdr_t opt_hdr;
  logic          val;
  modport in  (input  hdr, opt_hdr, val);
  modport out (output hdr, opt_hdr, val);
);

module dhcp_vlg (
  input logic clk,
  input logic rst,
  udp.in      rx,
  udp.out     tx,

  input  logic  ipv4_addr_req,
  output ipv4_t ipv4_addr,
  output logic  ipv4_addr_val,
  output logic  ipv4_addr_timeout,
  input  dev_t  dev
);

dhcp_vlg_core dhcp_vlg_core_inst (
  .clk (clk),
  .rst (rst),
  
  .ipv4_addr_req     (ipv4_addr_req),
  .ipv4_addr         (ipv4_addr),
  .ipv4_addr_val     (ipv4_addr_val),
  .ipv4_addr_timeout (ipv4_addr_timeout),
  .dev               (dev),
  .tx                (dhcp_rx),
  .rx                (dhcp_tx)
);

dhcp_vlg_rx dhcp_vlg_rx_inst (
  .clk (clk),
  .rst (rst),
  .dev (dev),
  .rx  (dhcp_rx),
  .udp (udp_rx)
);

dhcp_vlg_tx dhcp_vlg_tx_inst (
  .clk (clk),
  .rst (rst),
  .dev (dev),
  .tx  (dhcp_tx),
  .udp (udp_tx)
);

endmodule : dhcp_vlg

import udp_vlg_pkg::*;
import dhcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import eth_vlg_pkg::*;

module dhcp_vlg_rx (
  input logic clk,
  input logic rst,
  input dev_t dev,
  udp.in      udp
);

parameter HDR_LEN = 172;

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr_done  <= 0;
    receiving <= 0;
    err_len   <= 0;
  end
  else begin
    if (udp.sof && (udp.udp_hdr.src_port == DHCP_CLI_PORT)) begin
      receiving <= 1;
    end
    if (udp.eof) receiving <= 0;
    hdr[1:HDR_LEN-1] <= hdr[0:HDR_LEN-2];
    if (receiving && byte_cnt == HDR_LEN) hdr_done <= 1;
    if (receiving && udp.eof && byte_cnt != rx.payload_length) err_len <= !rx.eof;
  end
end

always @ (posedge clk) begin
  if (fsm_rst) begin
    dhcp.dhcp_hdr.dhcp_op     <= 0;
    dhcp.dhcp_hdr.dhcp_htype  <= 0;
    dhcp.dhcp_hdr.dhcp_hlen   <= 0;
    dhcp.dhcp_hdr.dhcp_hops   <= 0;
    dhcp.dhcp_hdr.dhcp_xid    <= 0;
    dhcp.dhcp_hdr.dhcp_secs   <= 0;
    dhcp.dhcp_hdr.dhcp_flags  <= 0;
    dhcp.dhcp_hdr.dhcp_ciaddr <= 0;
    dhcp.dhcp_hdr.dhcp_yiaddr <= 0;
    dhcp.dhcp_hdr.dhcp_siaddr <= 0;
    dhcp.dhcp_hdr.dhcp_giaddr <= 0;
    dhcp.dhcp_hdr.dhcp_chaddr <= 0;
    dhcp.dhcp_hdr.dhcp_sname  <= 0;
    dhcp.dhcp_hdr.dhcp_file   <= 0;
    opt_len                   <= 0;
    opt_en                    <= 0;
    offset_val                <= 0;
    opt_field                 <= opt_field_kind;
  end
  else if (rx.v) begin
    if (byte_cnt == HDR_LEN - 1) begin
      dhcp.dhcp_hdr.dhcp_op     <= hdr[171];
      dhcp.dhcp_hdr.dhcp_htype  <= hdr[170];
      dhcp.dhcp_hdr.dhcp_hlen   <= hdr[169];
      dhcp.dhcp_hdr.dhcp_hops   <= hdr[168];
      dhcp.dhcp_hdr.dhcp_xid    <= hdr[167:164];
      dhcp.dhcp_hdr.dhcp_secs   <= hdr[163:162];
      dhcp.dhcp_hdr.dhcp_flags  <= hdr[161:160];
      dhcp.dhcp_hdr.dhcp_ciaddr <= hdr[159:156];
      dhcp.dhcp_hdr.dhcp_yiaddr <= hdr[155:152];
      dhcp.dhcp_hdr.dhcp_siaddr <= hdr[151:148];
      dhcp.dhcp_hdr.dhcp_giaddr <= hdr[147:144];
      dhcp.dhcp_hdr.dhcp_chaddr <= hdr[143:128];
      dhcp.dhcp_hdr.dhcp_sname  <= hdr[127:64];
      dhcp.dhcp_hdr.dhcp_file   <= hdr[63:0];
      opt_en <= 1; // start analyzing options
    end
    if (opt_en) begin
      case (opt_field)
        opt_field_kind : begin
          case (rx.d)
            DHCP_OPT_MESSAGE_TYPE : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_message_type;
            end
            DHCP_OPT_SUBNET_MASK : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_subnet_mask;
            end
            DHCP_OPT_RENEWAL_TIME : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_renewal_time; 
            end
            DHCP_OPT_REBINDING_TIME : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_rebinding_time;
            end
            DHCP_OPT_IP_ADDR_LEASE_TIME : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_ip_addr_lease_time;  
            end
            DHCP_OPT_DHCP_CLIENT_ID : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_dhcp_client_id;
            end
            DHCP_OPT_DHCP_SERVER_ID : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_dhcp_server_id;
            end
            DHCP_OPT_ROUTER : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_router;
            end
            DHCP_OPT_DOMAIN_NAME_SERVER : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_domain_name_server;
            end
            DHCP_OPT_DOMAIN_NAME : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_domain_name;
            end
            DHCP_OPT_END : begin
              done <= 1;
              opt_field <= opt_field_kind;
              cur_opt <= dhcp_opt_end;
            end
            default : begin
              opt_field <= opt_field_len;
            end
          endcase
          opt_byte_cnt <= 0;
        end
        opt_field_len : begin
          opt_len <= rx.d - 2; // exclude kind and length bytes and 1 byte due to delay
          opt_field <= (rx.d == 2) ? opt_field_kind : opt_field_data;
        end
        opt_field_data : begin
          if (opt_byte_cnt == opt_len-1) opt_field <= opt_field_kind;
          opt_byte_cnt <= opt_byte_cnt + 1;
        end
      endcase
    end
  end
end


assign dhcp.err = (err_len || rx.err);
always @ (posedge clk) fsm_rst <= (dhcp.done || rst || dhcp.err || dhcp.eof);

assign hdr[0] = rx.d;

// Output 

always @ (posedge clk) begin
  if (fsm_rst)  begin
      dhcp.d    <= 0;
    dhcp.sof  <= 0;
    dhcp.eof  <= 0;
    byte_cnt <= 0;
  end
  else begin
    if (rx.v && (rx.ipv4_hdr.proto == DHCP)) byte_cnt <= byte_cnt + 1;
    dhcp.d <= rx.d;
    dhcp.sof <= (offset_val && byte_cnt == offset_bytes && dhcp.dhcp_hdr.dst_port == port);
    dhcp.eof <= receiving && rx.eof;
  end
end

endmodule

 

  





module dhcp_vlg_tx (
  input logic clk,
  input logic rst,
  input dev_t dev,
  udp.in      rx,
  udp.out     udp
);
localparam int DHCP_PACKET_LEN = 342;
always_ff @ (posedge clk) begin
  if (rst) begin
    
  end
  else begin
    case (fsm)
      idle_s : begin
        if (req_ipv4_addr) begin
          tx.len <= DHCP_PACKET_LEN

        end
      end
    endcase
  end
end

logic [0:14][31:0] opt_hdr_proto;

always @ (posedge clk) begin
  if (fsm_rst) begin
    opt           <= dhcp_opt_mss;
    opt_addr      <= 0;
    opt_byte_cnt  <= 0;
    opt_hdr_pres  <= 0;
    opt_hdr_proto <= 0;
    opt_len_32    <= 0;
    opt_assembled <= 0;
    shift_opt     <= 0;
    busy      <= 0;
  end
  else begin
    if (dhcp.dhcp_hdr_v) begin // transmit starts here
      busy <= 1;  // set busy flag and reset it when done transmitting. needed for server and queue to wait for sending next packet 
      shift_opt <= 1; // After options and header are set, compose a valid option header
      opt_hdr_pres <= {
        dhcp.dhcp_opt_hdr.dhcp_opt_message_type.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_subnet_mask.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_renewal_time.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_rebinding_time.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_ip_addr_lease_time.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_dhcp_server_id.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_router.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_domain_name_server.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_domain_name.present,
        dhcp.dhcp_opt_hdr.dhcp_opt_end.present};    
      };
      opt_hdr_proto <= {
        dhcp.dhcp_opt_hdr.dhcp_opt_message_type.msgt,
        dhcp.dhcp_opt_hdr.dhcp_opt_subnet_mask.netmsk,
        dhcp.dhcp_opt_hdr.dhcp_opt_renewal_time.renewtim,
        dhcp.dhcp_opt_hdr.dhcp_opt_rebinding_time.rebindtim,
        dhcp.dhcp_opt_hdr.dhcp_opt_ip_addr_lease_time.ipleasetim,
        dhcp.dhcp_opt_hdr.dhcp_opt_dhcp_server_id.dhcpsrvid,
        dhcp.dhcp_opt_hdr.dhcp_opt_router.router,
        dhcp.dhcp_opt_hdr.dhcp_opt_domain_name_server.dns,
        dhcp.dhcp_opt_hdr.dhcp_opt_domain_name.domname,
        dhcp.dhcp_opt_hdr.dhcp_opt_end.optend}; // Set which option fields are present
    end
    else if (shift_opt) begin // create valid options to concat it with dhcp header
      opt_byte_cnt <= opt_byte_cnt + 1;
      opt_hdr_proto[0:13] <= opt_hdr_proto[1:14];
      opt_hdr_pres[0:13] <= opt_hdr_pres[1:14];
      if (opt_hdr_pres[0]) begin // Shift by 32 bits
        opt_len_32 <= opt_len_32 + 1;
        opt_hdr[0:3] <= opt_hdr_proto[0];
        opt_hdr[4:39] <= opt_hdr[0:35];
      end
      if (opt_byte_cnt == 14) begin
        opt_assembled <= 1;
        shift_opt <= 0;
      end
    end
  end
end


endmodule

