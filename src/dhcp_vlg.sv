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
  ipv4_t           src_ip;
  ipv4_t           dst_ip;

  modport in  (input hdr, opt_hdr, opt_pres, val, err, src_ip, dst_ip, output done);
  modport out (output hdr, opt_hdr, opt_pres, val, err, src_ip, dst_ip, input done);
endinterface : dhcp

module dhcp_vlg #(
  parameter mac_addr_t MAC_ADDR    = 0,
  parameter [7:0]                      DOMAIN_NAME_LEN = 3,
  parameter [7:0]                      HOSTNAME_LEN    = 10,
  parameter [7:0]                      FQDN_LEN        = 11,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME     = "nya",
  parameter [0:HOSTNAME_LEN-1]  [7:0]  HOSTNAME        = "localnyann",
  parameter [0:FQDN_LEN-1]      [7:0]  FQDN            = "www.nya.com"
)
(
  input logic clk,
  input logic rst,
  udp.out_tx  tx,
  udp.in_rx   rx,
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
  .MAC_ADDR         (MAC_ADDR),
  .DOMAIN_NAME_LEN  (DOMAIN_NAME_LEN),
  .HOSTNAME_LEN     (HOSTNAME_LEN),
  .FQDN_LEN         (FQDN_LEN),
  .DOMAIN_NAME      (DOMAIN_NAME),
  .HOSTNAME         (HOSTNAME),
  .FQDN             (FQDN)
) dhcp_vlg_core_inst (
  .clk              (clk),
  .rst              (rst),
  
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

dhcp_vlg_tx #(
  .DOMAIN_NAME      (DOMAIN_NAME),
  .HOSTNAME         (HOSTNAME),
  .FQDN             (FQDN),
  .DOMAIN_NAME_LEN  (DOMAIN_NAME_LEN),
  .HOSTNAME_LEN     (HOSTNAME_LEN),
  .FQDN_LEN         (FQDN_LEN)
) dhcp_vlg_tx_inst (
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
  udp.in_rx   rx
);

logic [DHCP_HDR_LEN-1:0][7:0] hdr;
logic [7:0][dhcp_vlg_pkg::OPT_LEN-1:0] opt_data;
logic [$clog2(dhcp_vlg_pkg::OPT_LEN+1)-1:0] opt_cnt;

logic [15:0] byte_cnt; // DHCP packets can have 
logic [7:0] opt_len;

logic fsm_rst, err, done, receiving, hdr_done, err_len, opt_en;
dhcp_opt_t cur_opt;
//always @ (posedge clk) begin
//  if (rst) fsm_rst <= 1;
//  else fsm_rst <= err || done;
//end

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
    hdr[DHCP_HDR_LEN-2:0] <= hdr[DHCP_HDR_LEN-1:1];
    if (receiving && byte_cnt == DHCP_HDR_LEN) hdr_done <= 1;
    if (receiving && rx.eof && byte_cnt != rx.udp_hdr.length) err_len <= 1;
  end
end

assign hdr[DHCP_HDR_LEN-1] = rx.dat;
dhcp_opt_field_t opt_field;

always @ (posedge clk) fsm_rst <= (dhcp.done || rst || dhcp.err || err_len || done);

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
    opt_field                  <= dhcp_opt_field_kind;
  end
  else if (rx.val) begin
    if (byte_cnt == DHCP_HDR_LEN - 1) begin
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
        dhcp_opt_field_kind : begin
          case (rx.dat)
            DHCP_OPT_MESSAGE_TYPE : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_message_type;
            end
            DHCP_OPT_SUBNET_MASK : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_subnet_mask;
            end
            DHCP_OPT_RENEWAL_TIME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_renewal_time; 
            end
            DHCP_OPT_REBINDING_TIME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_rebinding_time;
            end
            DHCP_OPT_IP_ADDR_LEASE_TIME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_ip_addr_lease_time;  
            end
            DHCP_OPT_DHCP_CLIENT_ID : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_dhcp_client_id;
            end
            DHCP_OPT_DHCP_SERVER_ID : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_dhcp_server_id;
            end
            DHCP_OPT_ROUTER : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_router;
            end
            DHCP_OPT_DOMAIN_NAME_SERVER : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_domain_name_server;
            end
            DHCP_OPT_DOMAIN_NAME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_domain_name;
            end
            DHCP_OPT_END : begin
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
          opt_len <= rx.dat - 2; // exclude kind and length bytes and 1 byte due to delay
          opt_field <= (rx.dat == 2) ? dhcp_opt_field_kind : dhcp_opt_field_data;
        end
        dhcp_opt_field_data : begin
          if (opt_cnt == opt_len-1) opt_field <= dhcp_opt_field_kind;
          opt_cnt <= opt_cnt + 1;
        end
      endcase
    end
  end
end

// Output 

endmodule : dhcp_vlg_rx

module dhcp_vlg_tx #(
  parameter [7:0]                      DOMAIN_NAME_LEN = 9,
  parameter [7:0]                      HOSTNAME_LEN    = 8,
  parameter [7:0]                      FQDN_LEN        = 11,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME     = "nya", 
  parameter [0:HOSTNAME_LEN-1][7:0]    HOSTNAME        = "localnya",
  parameter [0:FQDN_LEN-1][7:0]        FQDN            = "www.nya.com"
)
(
  input logic clk,
  input logic rst,
  input dev_t dev,
  udp.out_tx  tx,
  dhcp.in     dhcp
);

logic str_en;

/*
logic [7:0] domain_name_len;
logic [dhcp_vlg_pkg::OPT_LEN-3:0] [7:0] domain_name_str;

logic [7:0] hostname_len;
logic [dhcp_vlg_pkg::OPT_LEN-3:0] [7:0] hostname_str;

logic [7:0] FQDN_len;
logic [dhcp_vlg_pkg::OPT_LEN-3:0] [7:0] FQDN_str;

logic str_en;

string_handler #(
  .MAX_LEN (dhcp_vlg_pkg::OPT_LEN-2)
)
string_handler_domain_name_inst (
  .clk (clk),
  .rst (rst),

  .in  (DOMAIN_NAME),
  .out (domain_name_str),
  .len (domain_name_len),
  .val (),
  .en  (str_en)
);

string_handler #(
  .MAX_LEN (dhcp_vlg_pkg::OPT_LEN-2)
)
string_handler_hostname_inst (
  .clk (clk),
  .rst (rst),

  .in  (HOSTNAME),
  .out (hostname_str),
  .len (hostname_len),
  .val (),
  .en  (str_en)
);

string_handler #(
  .MAX_LEN (dhcp_vlg_pkg::OPT_LEN-2)
)
string_handler_FQDN_inst (
  .clk (clk),
  .rst (rst),

  .in  (FQDN),
  .out (FQDN_str),
  .len (FQDN_len),
  .val (),
  .en  (str_en)
);
*/

logic fsm_rst, shift_opt;
logic busy, opt_rdy;

logic [dhcp_vlg_pkg::OPT_NUM-1:0][dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_hdr_proto; // 1 byte for end option
logic [0:dhcp_vlg_pkg::OPT_NUM-1][dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_hdr; // 1 byte for end option
logic [dhcp_vlg_pkg::OPT_NUM-1:0] dhcp_opt_pres;

logic [$clog2(dhcp_vlg_pkg::OPT_NUM+1)-1:0]     opt_cnt;
logic [$clog2(dhcp_vlg_pkg::OPT_TOT_LEN+1)-1:0] opt_len;

///////////////////////
// Options assembler //
///////////////////////
always @ (posedge clk) begin
  if (fsm_rst) begin
    opt_cnt       <= 0;
    dhcp_opt_pres <= 0;
    opt_hdr_proto <= 0;
    opt_rdy       <= 0;
    shift_opt     <= 0;
    busy          <= 0;
    opt_hdr       <= 0;
    opt_len       <= 0;
    str_en        <= 0;
  end
  else begin
    str_en <= 1;
    if (dhcp.val) begin // transmit starts here
   // $display("----> FQDN: %s, length: %d", FQDN, FQDN_LEN);
      opt_len <= 0;
      busy <= 1;  // set busy flag and reset it when done tx_en. needed for server and queue to wait for sending next packet 
      shift_opt <= 1; // After options and header are set, compose a valid option header
      opt_hdr_proto <= {         
        {DHCP_OPT_MESSAGE_TYPE,                     DHCP_OPT_MESSAGE_TYPE_LEN,       dhcp.opt_hdr.dhcp_opt_message_type,       {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_MESSAGE_TYPE_LEN       -2){DHCP_OPT_PAD}}},
        {DHCP_OPT_SUBNET_MASK,                      DHCP_OPT_SUBNET_MASK_LEN,        dhcp.opt_hdr.dhcp_opt_subnet_mask,        {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_SUBNET_MASK_LEN        -2){DHCP_OPT_PAD}}},
        {DHCP_OPT_RENEWAL_TIME,                     DHCP_OPT_RENEWAL_TIME_LEN,       dhcp.opt_hdr.dhcp_opt_renewal_time,       {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_RENEWAL_TIME_LEN       -2){DHCP_OPT_PAD}}}, 
        {DHCP_OPT_REBINDING_TIME,                   DHCP_OPT_REBINDING_TIME_LEN,     dhcp.opt_hdr.dhcp_opt_rebinding_time,     {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_REBINDING_TIME_LEN     -2){DHCP_OPT_PAD}}},                      
        {DHCP_OPT_IP_ADDR_LEASE_TIME,               DHCP_OPT_IP_ADDR_LEASE_TIME_LEN, dhcp.opt_hdr.dhcp_opt_ip_addr_lease_time, {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_IP_ADDR_LEASE_TIME_LEN -2){DHCP_OPT_PAD}}},               
        {DHCP_OPT_DHCP_SERVER_ID,                   DHCP_OPT_DHCP_SERVER_ID_LEN,     dhcp.opt_hdr.dhcp_opt_dhcp_server_id,     {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DHCP_SERVER_ID_LEN     -2){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DHCP_CLIENT_ID,                   DHCP_OPT_DHCP_CLIENT_ID_LEN,     dhcp.opt_hdr.dhcp_opt_dhcp_client_id,     {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DHCP_CLIENT_ID_LEN     -2){DHCP_OPT_PAD}}},           
        {DHCP_OPT_HOSTNAME,                         HOSTNAME_LEN,                    HOSTNAME,                                 {(dhcp_vlg_pkg::OPT_LEN-HOSTNAME_LEN                    -2){DHCP_OPT_PAD}}},  
        {DHCP_OPT_ROUTER,                           DHCP_OPT_ROUTER_LEN,             dhcp.opt_hdr.dhcp_opt_router,             {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_ROUTER_LEN             -2){DHCP_OPT_PAD}}},    
        {DHCP_OPT_DOMAIN_NAME_SERVER,               DHCP_OPT_DOMAIN_NAME_SERVER_LEN, dhcp.opt_hdr.dhcp_opt_domain_name_server, {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DOMAIN_NAME_SERVER_LEN -2){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DOMAIN_NAME,                      DOMAIN_NAME_LEN,                 DOMAIN_NAME,                              {(dhcp_vlg_pkg::OPT_LEN-DOMAIN_NAME_LEN                 -2){DHCP_OPT_PAD}}},                  
        {DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME,      FQDN_LEN,                        FQDN,                                     {(dhcp_vlg_pkg::OPT_LEN-FQDN_LEN                        -2){DHCP_OPT_PAD}}},   
        {{(dhcp_vlg_pkg::OPT_LEN-1){DHCP_OPT_PAD}}, DHCP_OPT_END                                                                                                                                         }
      };
      dhcp_opt_pres <= dhcp.opt_pres;
    end
    else if (shift_opt) begin // create valid options to concat them with dhcp header      
      opt_cnt <= opt_cnt + 1;
      dhcp_opt_pres[dhcp_vlg_pkg::OPT_NUM-2:0] <= dhcp_opt_pres[dhcp_vlg_pkg::OPT_NUM-1:1];
      opt_hdr_proto[dhcp_vlg_pkg::OPT_NUM-2:0] <= opt_hdr_proto[dhcp_vlg_pkg::OPT_NUM-1:1];
      if (dhcp_opt_pres[0]) begin // Shift by 32 bits
        opt_len <= opt_len + dhcp_vlg_pkg::OPT_LEN;
        opt_hdr[1:dhcp_vlg_pkg::OPT_NUM-1] <= opt_hdr[0:dhcp_vlg_pkg::OPT_NUM-2];
        opt_hdr[0] <= opt_hdr_proto[0];
      end
      if (opt_cnt == dhcp_vlg_pkg::OPT_NUM-1) begin
        opt_rdy <= 1;
        shift_opt <= 0;
      end
    end
  end
end

//////////////////////
// Transmit control //
//////////////////////

logic tx_en;
logic [15:0] byte_cnt;
logic [0:DHCP_HDR_LEN+dhcp_vlg_pkg::OPT_TOT_LEN-1][7:0] hdr;
logic rst_reg;
assign fsm_rst = rst || rst_reg; 

always @ (posedge clk) begin
  if (fsm_rst || rst) begin
    rst_reg      <= 0;
    tx_en        <= 0;
    byte_cnt     <= 0;
    tx.rdy       <= 0;
    tx.sof       <= 0;
    tx.val       <= 0;
    tx.dat       <= 0;
    tx.eof       <= 0;
    tx.broadcast <= 1;
    hdr          <= 0;
  end
  else begin
    if (dhcp.val) hdr[0:DHCP_HDR_LEN-1] <= dhcp.hdr;
    if (tx.req) begin
      tx.val <= 1;
      tx.sof <= (byte_cnt == 0);
      hdr[0:dhcp_vlg_pkg::HDR_TOT_LEN-2] <= hdr[1:dhcp_vlg_pkg::HDR_TOT_LEN-1];
      byte_cnt <= byte_cnt + 1;
      tx.dat <= hdr[0];
      if (byte_cnt == DHCP_HDR_LEN + opt_len - 1) begin // 1 last byte for end option
        rst_reg <= 1;
        tx.eof  <= 1;
      end
    end
    else if (opt_rdy) begin
      tx.rdy <= 1;
      hdr[DHCP_HDR_LEN:dhcp_vlg_pkg::HDR_TOT_LEN-1] <= opt_hdr;
      tx.udp_hdr.src_port <= DHCP_CLI_PORT;
      tx.udp_hdr.dst_port <= DHCP_SRV_PORT;
      tx.udp_hdr.length   <= DHCP_HDR_LEN + udp_vlg_pkg::UDP_HDR_LEN + opt_len; // 1 for end option
      tx.udp_hdr.chsum    <= 0; // checksum not used
      tx.ipv4_hdr.src_ip  <= dhcp.src_ip;
      tx.ipv4_hdr.dst_ip  <= dhcp.dst_ip;
      tx.ipv4_hdr.id      <= 1234; // todo: prbs
      tx.broadcast        <= 1;
    end
  end
end

endmodule

module string_handler #(
  parameter int MAX_LEN = 16
)
(
  input  logic clk,
  input  logic rst,

  input  logic [MAX_LEN-1:0][7:0]      in,
  output logic [MAX_LEN-1:0][7:0]      out,
  output logic [$clog2(MAX_LEN+1)-1:0] len,
  output logic                         val,
  input  logic                         en
);

logic [$clog2(MAX_LEN+1)-1:0] ctr;
logic shift;
logic [MAX_LEN-1:0][7:0] in_reg;

always @ (posedge clk) begin
  if (rst) begin
    out <= 0;
    len <= 0;
    val <= 0;
    ctr <= 0;
    shift <= 0; 
  end
  else if (en) begin
    shift <= 1;
    if (shift) begin
      if (in_reg[MAX_LEN-1] != 0) begin
        val <= 1;
        if (!val) out <= in_reg;
        len <= MAX_LEN - ctr;
      end
      else begin
        in_reg[MAX_LEN-1:1] <= in_reg[MAX_LEN-2:0];
        ctr <= (ctr == MAX_LEN || val) ? ctr : ctr + 1;
      end
    end
    else in_reg <= in;
  end
end

endmodule : string_handler
