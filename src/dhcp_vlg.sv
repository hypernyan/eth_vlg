import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface dhcp;
  dhcp_hdr_t       hdr; // Packed header
  dhcp_opt_hdr_t   opt_hdr; // Packed options header
  dhcp_opt_pres_t  opt_pres;
  dhcp_opt_len_t   opt_len;
  logic            val;
  logic            done;
  logic            err;
  ipv4_t           src_ip;
  ipv4_t           dst_ip;

  modport in  (input hdr, opt_hdr, opt_pres, opt_len, val, err, src_ip, dst_ip, output done);
  modport out (output hdr, opt_hdr, opt_pres, opt_len, val, err, src_ip, dst_ip, input done);
endinterface : dhcp

module dhcp_vlg #(
  parameter mac_addr_t                 MAC_ADDR        = 0,
  parameter [7:0]                      DOMAIN_NAME_LEN = 3,
  parameter [7:0]                      HOSTNAME_LEN    = 10,
  parameter [7:0]                      FQDN_LEN        = 9,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME     = "nya",
  parameter [0:HOSTNAME_LEN-1]  [7:0]  HOSTNAME        = "localnyann",
  parameter [0:FQDN_LEN-1]      [7:0]  FQDN            = "fdqnya",
  parameter int                        TIMEOUT         = 1250000000,
  parameter bit                        ENABLE          = 1,
  parameter int                        RETRIES         = 3
)
(
  input logic clk,
  input logic rst,
  udp.out_tx  tx,
  udp.in_rx   rx,

  output logic   ready,
  output logic   error,
  // DHCP related
  input  ipv4_t  preferred_ipv4,
  output ipv4_t  assigned_ipv4,

  output logic   router_ipv4_addr_val,
  output ipv4_t  router_ipv4_addr,
   
  output logic   subnet_mask_val,
  output ipv4_t  subnet_mask,

  output logic   dhcp_success,
  output logic   dhcp_timeout

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
  .FQDN             (FQDN),
  .TIMEOUT          (TIMEOUT),
  .ENABLE           (ENABLE),
  .RETRIES          (RETRIES)
) dhcp_vlg_core_inst (
  .clk                  (clk),
  .rst                  (rst),
  
  .rx                   (dhcp_rx),
  .tx                   (dhcp_tx),
  .router_ipv4_addr_val (router_ipv4_addr_val),
  .router_ipv4_addr     (router_ipv4_addr),
  .subnet_mask_val      (subnet_mask_val),
  .subnet_mask          (subnet_mask),

  .ready          (ready),
  .error          (error),
  // DHCP related
  .preferred_ipv4 (preferred_ipv4),
  .assigned_ipv4  (assigned_ipv4),
  .dhcp_success   (dhcp_success),
  .dhcp_timeout   (dhcp_timeout)
);

dhcp_vlg_rx dhcp_vlg_rx_inst (
  .clk  (clk),
  .rst  (rst),
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
  dhcp.out    dhcp,
  udp.in_rx   rx
);

logic [DHCP_HDR_LEN-1:0][7:0] hdr;
logic [dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_data;
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
    dhcp.err  <= 0;
    byte_cnt  <= 0;
  end
  else begin
    if (rx.sof && (rx.udp_hdr.dst_port == dhcp_vlg_pkg::DHCP_CLI_PORT) && (rx.udp_hdr.src_port == dhcp_vlg_pkg::DHCP_SRV_PORT)) begin
      $display("DHCP RX");
      receiving <= 1;
    end
    if (rx.val) byte_cnt <= byte_cnt + 1;
    if (rx.eof) receiving <= 0;
    hdr[DHCP_HDR_LEN-1:1] <= hdr[DHCP_HDR_LEN-2:0];
    if (receiving && byte_cnt == DHCP_HDR_LEN) hdr_done <= 1;
  end
end

assign hdr[0] = rx.dat;
dhcp_opt_field_t opt_field;
always @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= (dhcp.err || err_len || done || rx.eof);

always @ (posedge clk) begin
  if (fsm_rst) begin
    opt_len       <= 0;
    opt_en        <= 0;
    done          <= 0;
    opt_data      <= 0;
    dhcp.hdr      <= 0;
    dhcp.val      <= 0;
    dhcp.opt_hdr  <= 0;
    dhcp.opt_pres <= 0;
    dhcp.opt_len  <= 0;
    opt_field     <= dhcp_opt_field_kind;
    cur_opt       <= dhcp_opt_message_type;
    opt_cnt       <= 0;
  end
  else if (rx.val) begin
    if (byte_cnt == DHCP_HDR_LEN - 1) begin
      dhcp.hdr <= hdr;
      opt_en <= 1; // start analyzing options
      opt_data <= 0;
    end
    if (opt_en) begin
      case (opt_field)
        dhcp_opt_field_kind : begin
          opt_data <= 0;
          case (rx.dat)
            DHCP_OPT_MESSAGE_TYPE : begin
              $display("msgt option: %d", rx.dat);
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_message_type;
              dhcp.opt_pres.dhcp_opt_message_type_pres <= 1;
            end
            DHCP_OPT_SUBNET_MASK : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_subnet_mask;
              dhcp.opt_pres.dhcp_opt_subnet_mask_pres <= 1;
            end
            DHCP_OPT_RENEWAL_TIME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_renewal_time; 
              dhcp.opt_pres.dhcp_opt_renewal_time_pres <= 1;
            end
            DHCP_OPT_REBINDING_TIME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_rebinding_time;
              dhcp.opt_pres.dhcp_opt_rebinding_time_pres <= 1;
            end
            DHCP_OPT_IP_ADDR_LEASE_TIME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_ip_addr_lease_time;  
              dhcp.opt_pres.dhcp_opt_ip_addr_lease_time_pres <= 1;
            end
            DHCP_OPT_REQUESTED_IP_ADDRESS : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_requested_ip_address;  
              dhcp.opt_pres.dhcp_opt_requested_ip_address_pres <= 1;             
            end
            DHCP_OPT_DHCP_CLIENT_ID : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_dhcp_client_id;
              dhcp.opt_pres.dhcp_opt_dhcp_client_id_pres <= 1;
            end
            DHCP_OPT_DHCP_SERVER_ID : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_dhcp_server_id;
              dhcp.opt_pres.dhcp_opt_dhcp_server_id_pres <= 1;
            end
            DHCP_OPT_ROUTER : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_router;
              dhcp.opt_pres.dhcp_opt_router_pres <= 1;
            end
            DHCP_OPT_DOMAIN_NAME_SERVER : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_domain_name_server;
              dhcp.opt_pres.dhcp_opt_domain_name_server_pres <= 1;
            end
            DHCP_OPT_DOMAIN_NAME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_domain_name;
              dhcp.opt_pres.dhcp_opt_domain_name_pres <= 1;
            end
            DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_fully_qualified_domain_name;
              dhcp.opt_pres.dhcp_opt_fully_qualified_domain_name_pres <= 1;
            end
            DHCP_OPT_HOSTNAME : begin
              opt_field <= dhcp_opt_field_len;
              cur_opt <= dhcp_opt_hostname;
              dhcp.opt_pres.dhcp_opt_hostname_pres <= 1;
            end                   
            DHCP_OPT_PAD : begin
              opt_field <= dhcp_opt_field_kind;
            end
            DHCP_OPT_END : begin
              dhcp.val <= 1;
              done <= 1;
              opt_field <= dhcp_opt_field_kind;
              cur_opt <= dhcp_opt_end;
            end
            default : begin
              $display("unknown option: %d", rx.dat);
              opt_field <= dhcp_opt_field_len;
            end
          endcase
          opt_cnt <= 0;
        end
        dhcp_opt_field_len : begin
         $display("len option: %d", rx.dat);
          case (cur_opt)
            dhcp_opt_hostname                    : dhcp.opt_len.dhcp_opt_hostname_len <= rx.dat; 
            dhcp_opt_domain_name                 : dhcp.opt_len.dhcp_opt_domain_name_len <= rx.dat; 
            dhcp_opt_fully_qualified_domain_name : dhcp.opt_len.dhcp_opt_fully_qualified_domain_name_len <= rx.dat; 
          endcase
          opt_len <= rx.dat;
          opt_field <= (rx.dat == 0) ? dhcp_opt_field_kind : dhcp_opt_field_data;
        end
        dhcp_opt_field_data : begin
           $display("data option: %d", rx.dat);
           opt_data[0] <= rx.dat;
           opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:1] <= opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-2:0];
          if (opt_cnt == opt_len-1) begin
            opt_field <= dhcp_opt_field_kind;
            case (cur_opt) 
              dhcp_opt_message_type                : dhcp.opt_hdr.dhcp_opt_message_type                <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_subnet_mask                 : dhcp.opt_hdr.dhcp_opt_subnet_mask                 <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_renewal_time                : dhcp.opt_hdr.dhcp_opt_renewal_time                <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_rebinding_time              : dhcp.opt_hdr.dhcp_opt_rebinding_time              <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_ip_addr_lease_time          : dhcp.opt_hdr.dhcp_opt_ip_addr_lease_time          <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_requested_ip_address        : dhcp.opt_hdr.dhcp_opt_requested_ip_address        <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_dhcp_server_id              : dhcp.opt_hdr.dhcp_opt_dhcp_server_id              <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_dhcp_client_id              : dhcp.opt_hdr.dhcp_opt_dhcp_client_id              <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_hostname                    : dhcp.opt_hdr.dhcp_opt_hostname                    <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_router                      : dhcp.opt_hdr.dhcp_opt_router                      <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_domain_name_server          : dhcp.opt_hdr.dhcp_opt_domain_name_server          <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_domain_name                 : dhcp.opt_hdr.dhcp_opt_domain_name                 <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
              dhcp_opt_fully_qualified_domain_name : dhcp.opt_hdr.dhcp_opt_fully_qualified_domain_name <= {opt_data[dhcp_vlg_pkg::MAX_OPT_PAYLOAD-1:0], rx.dat};
            endcase
          end
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
  udp.out_tx  tx,
  dhcp.in     dhcp
);

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
  end
  else begin
    if (dhcp.val) begin // transmit starts here
   // $display("----> FQDN: %s, length: %d", FQDN, FQDN_LEN);
      opt_len <= 0;
      busy <= 1;  // set busy flag and reset it when done tx_en. needed for server and queue to wait for sending next packet 
      shift_opt <= 1; // After options and header are set, compose a valid option header
      opt_hdr_proto <= {         
        {DHCP_OPT_MESSAGE_TYPE,                     DHCP_OPT_MESSAGE_TYPE_LEN,                             dhcp.opt_hdr.dhcp_opt_message_type,         {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_MESSAGE_TYPE_LEN         - 2){DHCP_OPT_PAD}}},
        {DHCP_OPT_SUBNET_MASK,                      DHCP_OPT_SUBNET_MASK_LEN,                              dhcp.opt_hdr.dhcp_opt_subnet_mask,          {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_SUBNET_MASK_LEN          - 2){DHCP_OPT_PAD}}},
        {DHCP_OPT_RENEWAL_TIME,                     DHCP_OPT_RENEWAL_TIME_LEN,                             dhcp.opt_hdr.dhcp_opt_renewal_time,         {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_RENEWAL_TIME_LEN         - 2){DHCP_OPT_PAD}}}, 
        {DHCP_OPT_REBINDING_TIME,                   DHCP_OPT_REBINDING_TIME_LEN,                           dhcp.opt_hdr.dhcp_opt_rebinding_time,       {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_REBINDING_TIME_LEN       - 2){DHCP_OPT_PAD}}},                      
        {DHCP_OPT_IP_ADDR_LEASE_TIME,               DHCP_OPT_IP_ADDR_LEASE_TIME_LEN,                       dhcp.opt_hdr.dhcp_opt_ip_addr_lease_time,   {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_IP_ADDR_LEASE_TIME_LEN   - 2){DHCP_OPT_PAD}}},               
        {DHCP_OPT_REQUESTED_IP_ADDRESS,             DHCP_OPT_REQUESTED_IP_ADDRESS_LEN,                     dhcp.opt_hdr.dhcp_opt_requested_ip_address, {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_REQUESTED_IP_ADDRESS_LEN - 2){DHCP_OPT_PAD}}},               
        {DHCP_OPT_DHCP_SERVER_ID,                   DHCP_OPT_DHCP_SERVER_ID_LEN,                           dhcp.opt_hdr.dhcp_opt_dhcp_server_id,       {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DHCP_SERVER_ID_LEN       - 2){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DHCP_CLIENT_ID,                   DHCP_OPT_DHCP_CLIENT_ID_LEN,                           dhcp.opt_hdr.dhcp_opt_dhcp_client_id,       {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DHCP_CLIENT_ID_LEN       - 2){DHCP_OPT_PAD}}},           
        {DHCP_OPT_HOSTNAME,                         dhcp.opt_len.dhcp_opt_hostname_len,                    HOSTNAME,                                   {(dhcp_vlg_pkg::OPT_LEN-HOSTNAME_LEN                      - 2){DHCP_OPT_PAD}}},  
        {DHCP_OPT_ROUTER,                           DHCP_OPT_ROUTER_LEN,                                   dhcp.opt_hdr.dhcp_opt_router,               {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_ROUTER_LEN               - 2){DHCP_OPT_PAD}}},    
        {DHCP_OPT_DOMAIN_NAME_SERVER,               DHCP_OPT_DOMAIN_NAME_SERVER_LEN,                       dhcp.opt_hdr.dhcp_opt_domain_name_server,   {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DOMAIN_NAME_SERVER_LEN   - 2){DHCP_OPT_PAD}}},           
        {DHCP_OPT_DOMAIN_NAME,                      dhcp.opt_len.dhcp_opt_domain_name_len,                 DOMAIN_NAME,                                {(dhcp_vlg_pkg::OPT_LEN-DOMAIN_NAME_LEN                   - 2){DHCP_OPT_PAD}}},                  
        {DHCP_OPT_FULLY_QUALIFIED_DOMAIN_NAME,      dhcp.opt_len.dhcp_opt_fully_qualified_domain_name_len, FQDN,                                       {(dhcp_vlg_pkg::OPT_LEN-FQDN_LEN                          - 2){DHCP_OPT_PAD}}},   
        {{(dhcp_vlg_pkg::OPT_LEN-1){DHCP_OPT_PAD}}, DHCP_OPT_END}
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

import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import udp_vlg_pkg::*;
import eth_vlg_pkg::*;
import dhcp_vlg_pkg::*;

module dhcp_vlg_core #(
  parameter mac_addr_t MAC_ADDR = 0,
  parameter [7:0]                      HOSTNAME_LEN    = 0,
  parameter [7:0]                      DOMAIN_NAME_LEN = 0,
  parameter [7:0]                      FQDN_LEN        = 0,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME     = "",
  parameter [0:HOSTNAME_LEN-1]   [7:0] HOSTNAME        = "",
  parameter [0:FQDN_LEN-1]       [7:0] FQDN            = "",
  parameter int                        TIMEOUT         = 1250000000,
  parameter bit                        ENABLE          = 1,
  parameter int                        RETRIES         = 3
)
(
  input  logic  clk,
  input  logic  rst,

  output logic   ready,
  output logic   error,
  // DHCP related
  input  ipv4_t  preferred_ipv4,
  output ipv4_t  assigned_ipv4,
  output logic   dhcp_success,
  output logic   dhcp_timeout,

  output logic   router_ipv4_addr_val,
  output ipv4_t  router_ipv4_addr,
  output logic   subnet_mask_val,
  output ipv4_t  subnet_mask,
  dhcp.in        rx,
  dhcp.out       tx
);

parameter STARTUP_DELAY_TICKS = 1000;
logic fsm_rst;

enum logic [4:0] {idle_s, discover_s, offer_s, request_s, ack_s} fsm;

ipv4_t offered_ip;
ipv4_t server_ip; 
logic timeout;

logic [$clog2(TIMEOUT+1)-1:0] timeout_ctr;


logic [$clog2(STARTUP_DELAY_TICKS+1)-1:0] startup_ctr;
logic [$clog2(RETRIES+1)-1:0] tries;

always @ (posedge clk) begin
  if (fsm_rst) begin
    fsm                  <= idle_s;
    tx.hdr               <= 0;
    tx.opt_hdr           <= 0;
    tx.opt_pres          <= 0;
    tx.val               <= 0;
    timeout_ctr          <= 0;
    timeout              <= 0;
    assigned_ipv4        <= 0;
    router_ipv4_addr_val <= 0;
    subnet_mask_val      <= 0;
    router_ipv4_addr     <= 0;
    ready                <= 0;
    dhcp_success         <= 0;
    startup_ctr          <= 0;
    subnet_mask          <= 0;
  end
  else begin
    case (fsm)
      idle_s : begin
        startup_ctr <= startup_ctr + 1;
        if (startup_ctr == STARTUP_DELAY_TICKS && !ready) fsm <= discover_s;
      end
      discover_s : begin
        dhcp_success     <= 0;
        tx.val <= 1;

        tx.hdr.dhcp_op           <= dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REQUEST;
        tx.hdr.dhcp_htype        <= 1;
        tx.hdr.dhcp_hlen         <= 6;
        tx.hdr.dhcp_hops         <= 0;
        tx.hdr.dhcp_xid          <= 32'hdeadface;
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
        tx.opt_hdr.dhcp_opt_requested_ip_address              <= preferred_ipv4;
        tx.opt_hdr.dhcp_opt_dhcp_server_id                    <= 0;
        tx.opt_hdr.dhcp_opt_dhcp_client_id                    <= {1'b1, MAC_ADDR};
        tx.opt_hdr.dhcp_opt_router                            <= 0;
        tx.opt_hdr.dhcp_opt_domain_name_server                <= {8'h1, 8'h2, 8'h3, 8'h4};
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
        tx.opt_pres.dhcp_opt_fully_qualified_domain_name_pres <= 0;
        tx.opt_pres.dhcp_opt_end_pres                         <= 1;
        
        tx.src_ip                                             <= {8'h0, 8'h0, 8'h0, 8'h0};
        tx.dst_ip                                             <= {8'hff, 8'hff, 8'hff, 8'hff};

        fsm <= offer_s;
      end
      offer_s : begin
        tx.val <= 0;
        timeout_ctr <= timeout_ctr + 1;
        if (timeout_ctr == TIMEOUT) timeout <= 1;
        if (rx.val) begin
          if (rx.hdr.dhcp_xid == 32'hdeadface &&
              rx.hdr.dhcp_op == dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY &&
              rx.opt_pres.dhcp_opt_message_type_pres &&
              rx.opt_hdr.dhcp_opt_message_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_OFFER
          ) begin
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
        tx.hdr.dhcp_xid          <= 32'hdeadface;
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
        tx.opt_hdr.dhcp_opt_domain_name_server                <= {8'h1, 8'h2, 8'h3, 8'h4};
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
        tx.opt_pres.dhcp_opt_dhcp_server_id_pres              <= 1;
        tx.opt_pres.dhcp_opt_dhcp_client_id_pres              <= 1;
        tx.opt_pres.dhcp_opt_router_pres                      <= 0;
        tx.opt_pres.dhcp_opt_domain_name_server_pres          <= 0;
        tx.opt_pres.dhcp_opt_hostname_pres                    <= 1;
        tx.opt_pres.dhcp_opt_domain_name_pres                 <= 0;
        tx.opt_pres.dhcp_opt_fully_qualified_domain_name_pres <= 1;
        tx.opt_pres.dhcp_opt_end_pres                         <= 1;
        
        tx.src_ip                                             <= {8'h0, 8'h0, 8'h0, 8'h0};
        tx.dst_ip                                             <= ip_vlg_pkg::IPV4_BROADCAST;       

        fsm <= ack_s;
      end
      ack_s : begin
        tx.val <= 0;
        timeout_ctr <= timeout_ctr + 1;
        if (timeout_ctr == TIMEOUT) timeout <= 1;
        if (rx.val) begin
          if (rx.hdr.dhcp_xid == 32'hdeadface &&
              rx.hdr.dhcp_op == dhcp_vlg_pkg::DHCP_MSG_TYPE_BOOT_REPLY &&
              rx.opt_pres.dhcp_opt_message_type_pres &&
              rx.opt_hdr.dhcp_opt_message_type == dhcp_vlg_pkg::DHCP_MSG_TYPE_ACK
            ) begin
            dhcp_success <= 1;
            ready        <= 1;
            assigned_ipv4 <= rx.hdr.dhcp_nxt_cli_addr;
            fsm <= idle_s;
            if (rx.opt_pres.dhcp_opt_router_pres) begin
              router_ipv4_addr <= rx.opt_hdr.dhcp_opt_router;
              router_ipv4_addr_val <= 1;
            end
            if (rx.opt_pres.dhcp_opt_subnet_mask_pres) begin
              subnet_mask <= rx.opt_hdr.dhcp_opt_subnet_mask;
              subnet_mask_val <= 1;
            end
          end
        end
      end
    endcase
  end
end

always @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= timeout;

always @ (posedge clk) begin
  if (rst) begin
    tries <= 0;
    error <= 0;
    dhcp_timeout <= 0;
  end
  else begin
    if (fsm_rst && timeout) tries <= tries + 1;
    if (tries == RETRIES) begin
      error <= 1;
      dhcp_timeout <= 1;
    end
  end
end

endmodule : dhcp_vlg_core

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
