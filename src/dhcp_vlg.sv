import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface dhcp;
  dhcp_hdr_t       hdr; // Packed header
  dhcp_opt_hdr_t   opt_hdr; // Packed options header
  dhcp_opt_pres_t  opt_pres;
  logic            val;
  logic            done;
  logic            err;

  modport in  (input hdr, opt_hdr, opt_pres, val, err, output done);
  modport out (output hdr, opt_hdr, opt_pres, val, err, input done);
endinterface : dhcp

module dhcp_vlg #(
  parameter mac_addr_t MAC_ADDR = 0
)
(
  input logic clk,
  input logic rst,
  udp.in      rx,
  udp.out     tx,
  input dev_t dev,

  input  logic  ipv4_req,
  input  ipv4_t pref_ipv4,

  output ipv4_t ipv4_addr,
  output logic  ipv4_val,

  output logic  ok,
  output logic  timeout
);

dhcp dhcp_rx (.*);
dhcp dhcp_tx (.*);

dhcp_vlg_core #(
  .MAC_ADDR (MAC_ADDR)
)
dhcp_vlg_core_inst (
  .clk (clk),
  .rst (rst),
  
  .ipv4_req          (ipv4_req),
  .ipv4_addr         (ipv4_addr),
  .ipv4_addr_val     (ipv4_addr_val),
  .ipv4_addr_timeout (ipv4_addr_timeout),
  .ok                (ok),
  .timeout           (timeout),     
  .dev               (dev),
  .rx                (dhcp_rx),
  .tx                (dhcp_tx)
);

dhcp_vlg_rx dhcp_vlg_rx_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .dhcp (dhcp_rx),
  .rx   (rx)
);

dhcp_vlg_tx dhcp_vlg_tx_inst (
  .clk  (clk),
  .rst  (rst),
  .dev  (dev),
  .dhcp (dhcp_tx),
  .tx   (tx)
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
  dhcp.out    dhcp,
  udp.in      rx
);

logic [dhcp_vlg_pkg::HDR_LEN-1:0][7:0] hdr;
logic [7:0][dhcp_vlg_pkg::OPT_LEN-1:0] opt_data;
logic [$clog2(dhcp_vlg_pkg::OPT_LEN+1)-1:0] opt_cnt;

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
    if (rx.sof && (rx.udp_hdr.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT)) begin
      receiving <= 1;
    end
    if (rx.eof) receiving <= 0;
    hdr[dhcp_vlg_pkg::HDR_LEN-2:0] <= hdr[dhcp_vlg_pkg::HDR_LEN-1:1];
    if (receiving && byte_cnt == dhcp_vlg_pkg::HDR_LEN) hdr_done <= 1;
    if (receiving && rx.eof && byte_cnt != rx.udp_hdr.length) err_len <= 1;
  end
end

assign hdr[dhcp_vlg_pkg::HDR_LEN-1] = rx.d;

dhcp_opt_t cur_opt;

always @ (posedge clk) begin
  if (fsm_rst) begin
    dhcp.hdr.dhcp_op           <= 0;
    dhcp.hdr.dhcp_htype        <= 0;
    dhcp.hdr.dhcp_hlen         <= 0;
    dhcp.hdr.dhcp_hops         <= 0;
    dhcp.hdr.dhcp_xid          <= 0;
    dhcp.hdr.dhcp_secs         <= 0;
    dhcp.hdr.dhcp_flags        <= 0;
    dhcp.hdr.dhcp_cur_cli_addr <= 0;
    dhcp.hdr.dhcp_nxt_cli_addr <= 0;
    dhcp.hdr.dhcp_srv_ip_addr  <= 0;
    dhcp.hdr.dhcp_retrans_addr <= 0;
    dhcp.hdr.dhcp_chaddr       <= 0;
    dhcp.hdr.dhcp_sname        <= 0;
    dhcp.hdr.dhcp_file         <= 0;
    opt_len                    <= 0;
    opt_en                     <= 0;
    opt_field                  <= opt_field_kind;
  end
  else if (rx.v) begin
    if (byte_cnt == dhcp_vlg_pkg::HDR_LEN - 1) begin
      dhcp.hdr.dhcp_op           <= hdr[171];
      dhcp.hdr.dhcp_htype        <= hdr[170];
      dhcp.hdr.dhcp_hlen         <= hdr[169];
      dhcp.hdr.dhcp_hops         <= hdr[168];
      dhcp.hdr.dhcp_xid          <= hdr[167:164];
      dhcp.hdr.dhcp_secs         <= hdr[163:162];
      dhcp.hdr.dhcp_flags        <= hdr[161:160];
      dhcp.hdr.dhcp_cur_cli_addr <= hdr[159:156];
      dhcp.hdr.dhcp_nxt_cli_addr <= hdr[155:152];
      dhcp.hdr.dhcp_srv_ip_addr  <= hdr[151:148];
      dhcp.hdr.dhcp_retrans_addr <= hdr[147:144];
      dhcp.hdr.dhcp_chaddr       <= hdr[143:128];
      dhcp.hdr.dhcp_sname        <= hdr[127:64];
      dhcp.hdr.dhcp_file         <= hdr[63:0];
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
          opt_cnt <= 0;
        end
        opt_field_len : begin
          opt_len <= rx.d - 2; // exclude kind and length bytes and 1 byte due to delay
          opt_field <= (rx.d == 2) ? opt_field_kind : opt_field_data;
        end
        opt_field_data : begin
          if (opt_cnt == opt_len-1) opt_field <= opt_field_kind;
          opt_cnt <= opt_cnt + 1;
        end
      endcase
    end
  end
end

assign dhcp.err = (err_len || rx.err);
always @ (posedge clk) fsm_rst <= (dhcp.done || rst || dhcp.err);

// Output 

endmodule : dhcp_vlg_rx

module dhcp_vlg_tx (
  input logic clk,
  input logic rst,
  input dev_t dev,
  udp.out     tx,
  dhcp.in     dhcp
);

localparam int DHCP_PACKET_LEN = 342;
logic fsm_rst, shift_opt;
logic [3:0] opt_cnt;
logic [3:0] opt_len_32;
logic busy, opt_rdy;
dhcp_opt_t opt;

logic [0:dhcp_vlg_pkg::OPT_NUM-1][dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_hdr_proto, opt_hdr;
logic [0:dhcp_vlg_pkg::OPT_NUM-1] dhcp_opt_pres;


///////////////////////
// Options assembler //
///////////////////////

always @ (posedge clk) begin
  if (fsm_rst) begin
    opt_cnt       <= 0;
    dhcp_opt_pres <= 0;
    opt_hdr_proto <= 0;
    opt_len_32    <= 0;
    opt_rdy       <= 0;
    shift_opt     <= 0;
    busy          <= 0;
  end
  else begin
    if (dhcp.val) begin // transmit starts here
      busy <= 1;  // set busy flag and reset it when done transmitting. needed for server and queue to wait for sending next packet 
      shift_opt <= 1; // After options and header are set, compose a valid option header
      opt_hdr_proto <= {         
        {DHCP_OPT_MESSAGE_TYPE,                DHCP_OPT_MESSAGE_TYPE_LEN,                dhcp.opt_hdr.dhcp_opt_message_type,                 {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_MESSAGE_TYPE_LEN-2){8'haa}}},
        {DHCP_OPT_SUBNET_MASK,                 DHCP_OPT_SUBNET_MASK_LEN,                 dhcp.opt_hdr.dhcp_opt_subnet_mask,                  {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_SUBNET_MASK_LEN-2){DHCP_OPT_PAD}}},
        {DHCP_OPT_RENEWAL_TIME,                DHCP_OPT_RENEWAL_TIME_LEN,                dhcp.opt_hdr.dhcp_opt_renewal_time,                 {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_RENEWAL_TIME_LEN      -2){DHCP_OPT_PAD}}}, 
        {DHCP_OPT_REBINDING_TIME,              DHCP_OPT_REBINDING_TIME_LEN,              dhcp.opt_hdr.dhcp_opt_rebinding_time,               {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_REBINDING_TIME_LEN    -2){DHCP_OPT_PAD}}},                      
        {DHCP_OPT_IP_ADDR_LEASE_TIME,          DHCP_OPT_IP_ADDR_LEASE_TIME_LEN,          dhcp.opt_hdr.dhcp_opt_ip_addr_lease_time,           {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_IP_ADDR_LEASE_TIME_LEN-2){DHCP_OPT_PAD}}},               
        {DHCP_OPT_DHCP_SERVER_ID,              DHCP_OPT_DHCP_SERVER_ID_LEN,              dhcp.opt_hdr.dhcp_opt_dhcp_client_id,               {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DHCP_CLIENT_ID_LEN    -2){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DHCP_CLIENT_ID,              DHCP_OPT_DHCP_CLIENT_ID_LEN,              dhcp.opt_hdr.dhcp_opt_dhcp_server_id,               {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DHCP_SERVER_ID_LEN    -2){DHCP_OPT_PAD}}},           
        {DHCP_OPT_ROUTER,                      DHCP_OPT_ROUTER_LEN,                      dhcp.opt_hdr.dhcp_opt_router,                       {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_ROUTER_LEN            -2){DHCP_OPT_PAD}}},    
        {DHCP_OPT_DOMAIN_NAME_SERVER,          DHCP_OPT_DOMAIN_NAME_SERVER_LEN,          dhcp.opt_hdr.dhcp_opt_domain_name_server,           {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DOMAIN_NAME_SERVER_LEN-2){DHCP_OPT_PAD}}},  
        {DHCP_OPT_DOMAIN_NAME,                 DHCP_OPT_DOMAIN_NAME_LEN,                 dhcp.opt_hdr.dhcp_opt_domain_name                   }, //{(OPT_LEN-DHCP_OPT_DOMAIN_NAME_LEN-1){DHCP_OPT_PAD}}},
        {DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME, DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME_LEN, dhcp.opt_hdr.dhcp_opt_fully_qualified_domain_name,  {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME_LEN-2){8'hbb}}}
      };
      dhcp_opt_pres <= dhcp.opt_pres;
    end
    else if (shift_opt) begin // create valid options to concat them with dhcp header
      opt_cnt <= opt_cnt + 1;
      dhcp_opt_pres[0:dhcp_vlg_pkg::OPT_NUM-2] <= dhcp_opt_pres[1:dhcp_vlg_pkg::OPT_NUM-1];
      if (dhcp_opt_pres[0]) begin // Shift by 32 bits
        opt_len_32 <= opt_len_32 + 1;
      end
      if (opt_cnt == dhcp_vlg_pkg::OPT_NUM) begin
        opt_rdy <= 1;
        shift_opt <= 0;
      end
    end
  end
end

//////////////////////
// Transmit control //
//////////////////////
logic transmitting;
logic [15:0] byte_cnt;
logic [dhcp_vlg_pkg::HDR_LEN-1:0][7:0] hdr;
always @ (posedge clk) begin
  if (rst) begin
    transmitting <= 0;
  end
  else begin
    if (dhcp.val)
      hdr[dhcp_vlg_pkg::HDR_LEN-1:0] <= dhcp.hdr; //.dhcp_op;
      //hdr[170]      <= dhcp.hdr.dhcp_htype;
      //hdr[169]      <= dhcp.hdr.dhcp_hlen;
      //hdr[168]      <= dhcp.hdr.dhcp_hops;
      //hdr[167:164]  <= dhcp.hdr.dhcp_xid;
      //hdr[163:162]  <= dhcp.hdr.dhcp_secs;
      //hdr[161:160]  <= dhcp.hdr.dhcp_flags;
      //hdr[159:156]  <= dhcp.hdr.dhcp_cur_cli_addr;
      //hdr[155:152]  <= dhcp.hdr.dhcp_nxt_cli_addr;
      //hdr[151:148]   <= dhcp.hdr.dhcp_srv_ip_addr;
      //hdr[147:144]   <= dhcp.hdr.dhcp_retrans_addr;
      //hdr[143:128]   <= dhcp.hdr.dhcp_chaddr;
      //hdr[127:64]    <= dhcp.hdr.dhcp_sname;
      //hdr[63:0]      <= dhcp.hdr.dhcp_file;
    if (opt_rdy) begin
      transmitting <= 1;
    //  hdr[]
    end
    if (transmitting) begin
    //  hdr[171:1] <= hdr[170:0];
      byte_cnt <= byte_cnt + 1;
    end
  end
end

endmodule

