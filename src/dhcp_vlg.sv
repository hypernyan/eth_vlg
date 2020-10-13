import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface dhcp;
  dhcp_hdr_t     hdr;
  dhcp_opt_hdr_t opt_hdr;
  logic          val;
  modport in  (input  hdr, opt_hdr, val);
  modport out (output hdr, opt_hdr, val);

endinterface : dhcp

module dhcp_vlg (
  input logic clk,
  input logic rst,
  udp.in      rx,
  udp.out     tx,

  input  logic  dhcp_ipv4_req,
  input  ipv4_t dhcp_pref_ipv4,
    
  output ipv4_t dhcp_ipv4_addr,
  output logic  dhcp_ipv4_val,
  
  output logic  dhcp_ok,
  output logic  dhcp_timeout
);

dhcp_vlg_core dhcp_vlg_core_inst (
  .clk (clk),
  .rst (rst),
  
  .ipv4_req          (ipv4_req),
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
  .udp (rx)
);

dhcp_vlg_tx dhcp_vlg_tx_inst (
  .clk (clk),
  .rst (rst),
  .dev (dev),
  .tx  (dhcp_tx),
  .udp (tx)
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

logic [dhcp_vlg_pkg::HDR_LEN-1:0][7:0] hdr;
logic [7:0][dhcp_vlg_pkg::MAX_OPT_DATA_LEN-1:0] opt_data;
logic [$clog2(dhcp_vlg_pkg::MAX_OPT_DATA_LEN+1)-1:0] opt_byte_cnt;

logic [15:0] byte_cnt; // DHCP packets can have 
logic [7:0] opt_len;

logic fsm_rst, err, done, receiving, hdr_done, err_len, opt_en;
dhcp_opt_field_t opt_field;
always @ (posedge clk) begin
  if (rst) fsm_rst <= 1;
  else fsm_rst <= err || done;
end

always @ (posedge clk) begin
  if (fsm_rst) begin
    hdr_done  <= 0;
    receiving <= 0;
    err_len   <= 0;
  end
  else begin
    if (udp.sof && (udp.udp_hdr.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT)) begin
      receiving <= 1;
    end
    if (udp.eof) receiving <= 0;
    hdr[dhcp_vlg_pkg::HDR_LEN-2:0] <= hdr[dhcp_vlg_pkg::HDR_LEN-1:1];
    if (receiving && byte_cnt == dhcp_vlg_pkg::HDR_LEN) hdr_done <= 1;
    if (receiving && udp.eof && byte_cnt != rx.payload_length) err_len <= !rx.eof;
  end
end

assign hdr[dhcp_vlg_pkg::MAX_OPT_DATA_LEN] = rx.d;

dhcp_opt_t cur_opt;

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
    opt_field                 <= opt_field_kind;
  end
  else if (rx.v) begin
    if (byte_cnt == dhcp_vlg_pkg::HDR_LEN - 1) begin
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
            dhcp_vlg_pkg::DHCP_OPT_MESSAGE_TYPE : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_message_type;
            end
            dhcp_vlg_pkg::DHCP_OPT_SUBNET_MASK : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_subnet_mask;
            end
            dhcp_vlg_pkg::DHCP_OPT_RENEWAL_TIME : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_renewal_time; 
            end
            dhcp_vlg_pkg::DHCP_OPT_REBINDING_TIME : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_rebinding_time;
            end
            dhcp_vlg_pkg::DHCP_OPT_IP_ADDR_LEASE_TIME : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_ip_addr_lease_time;  
            end
            dhcp_vlg_pkg::DHCP_OPT_DHCP_CLIENT_ID : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_dhcp_client_id;
            end
            dhcp_vlg_pkg::DHCP_OPT_DHCP_SERVER_ID : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_dhcp_server_id;
            end
            dhcp_vlg_pkg::DHCP_OPT_ROUTER : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_router;
            end
            dhcp_vlg_pkg::DHCP_OPT_DOMAIN_NAME_SERVER : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_domain_name_server;
            end
            dhcp_vlg_pkg::DHCP_OPT_DOMAIN_NAME : begin
              opt_field <= opt_field_len;
              cur_opt <= dhcp_opt_domain_name;
            end
            dhcp_vlg_pkg::DHCP_OPT_END : begin
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


// Output 

endmodule : dhcp_vlg_rx

module dhcp_vlg_tx (
  input logic clk,
  input logic rst,
  input dev_t dev,
  udp.in      rx,
  udp.out     udp
);
localparam int DHCP_PACKET_LEN = 342;

logic [0:14][31:0] opt_hdr_proto;
logic fsm_rst, shift_opt;
logic [3:0] opt_byte_cnt;
logic [3:0] opt_len_32;
logic busy, opt_assembled;
dhcp_opt_pres_t dhcp_pres;
dhcp_opt_t opt;
logic [0:dhcp_vlg_pkg::MAX_OPT_DATA_LEN-1][7:0] opt_hdr;

always @ (posedge clk) begin
  if (fsm_rst) begin
    opt           <= dhcp_opt_message_type;
    opt_byte_cnt  <= 0;
    dhcp_pres     <= 0;
    opt_hdr_proto <= 0;
    opt_len_32    <= 0;
    opt_assembled <= 0;
    shift_opt     <= 0;
    busy          <= 0;
  end
  else begin
    if (dhcp.dhcp_hdr_v) begin // transmit starts here
      busy <= 1;  // set busy flag and reset it when done transmitting. needed for server and queue to wait for sending next packet 
      shift_opt <= 1; // After options and header are set, compose a valid option header
      dhcp_pres <= 
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
        dhcp.dhcp_opt_hdr.dhcp_opt_end.optend
      }; // Set which option fields are present
    end
    else if (shift_opt) begin // create valid options to concat it with dhcp header
      opt_byte_cnt <= opt_byte_cnt + 1;
      opt_hdr_proto[0:13] <= opt_hdr_proto[1:14];
      dhcp_pres[0:13] <= dhcp_pres[1:14];
      if (dhcp_pres[0]) begin // Shift by 32 bits
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

