
module dhcp_vlg_tx 
  import 
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    udp_vlg_pkg::*,
    eth_vlg_pkg::*,
    dhcp_vlg_pkg::*;
#(
  parameter [7:0]                      DOMAIN_NAME_LEN = 9,
  parameter [7:0]                      HOSTNAME_LEN    = 8,
  parameter [7:0]                      FQDN_LEN        = 11,
  parameter [DOMAIN_NAME_LEN-1:0][7:0] DOMAIN_NAME     = "nya", 
  parameter [HOSTNAME_LEN-1:0][7:0]    HOSTNAME        = "localnya",
  parameter [FQDN_LEN-1:0][7:0]        FQDN            = "www.nya.com",
  parameter mac_addr_t                 MAC_ADDR        = {8{8'hff}}

)
(
  input logic    clk,
  input logic    rst,
  udp_ifc.out_tx udp,
  dhcp_ifc.in    dhcp
);
  parameter int CONST_BYTES = 28;
  parameter int OPT_REG_BYTES = CONST_BYTES + HOSTNAME_LEN + DOMAIN_NAME_LEN + FQDN_LEN;

  logic fsm_rst;
  
  logic [DHCP_HDR_LEN-1:0] [7:0] hdr;
  logic [OPT_REG_BYTES-1:0][7:0] opt;       // composed options

  logic [$clog2(DHCP_HDR_TOT_LEN+OPT_REG_BYTES):0] byte_cnt;
  
  // logic resets itself after transmission

  ///////////////////////
  // Options assembler //
  ///////////////////////
  // Every option has length of OPT_LEN
  // And is padded by zeros if necessary

  parameter [7:0] DHCP_FQDN_FLAGS  = 8'b00000010;
  parameter [7:0] DHCP_FQDN_RCODE1 = 0;
  parameter [7:0] DHCP_FQDN_RCODE2 = 0;
  parameter [7:0] FQDN_TOT_LEN = FQDN_LEN + 3;

  always_ff @ (posedge clk) begin
    udp.meta.udp_hdr.src_port <= DHCP_CLI_PORT;
    udp.meta.udp_hdr.dst_port <= DHCP_SRV_PORT;
    udp.meta.udp_hdr.cks      <= 0; // checksum skipped
    udp.meta.udp_hdr.length   <= DHCP_HDR_TOT_LEN + OPT_REG_BYTES + udp_vlg_pkg::UDP_HDR_LEN;
    udp.meta.mac_known        <= 1;
    udp.meta.mac_hdr.dst_mac  <= mac_vlg_pkg::MAC_BROADCAST;
    udp.meta.ipv4_hdr.src_ip  <= dhcp.src_ip;
    udp.meta.ipv4_hdr.dst_ip  <= dhcp.dst_ip;
    udp.meta.ipv4_hdr.id      <= dhcp.ipv4_id;
  end

  enum logic [3:0] {
    tx_hdr,
    tx_zero,
    tx_cookie,
    tx_opt
  } cur_tx;
  
  parameter DHCP_OPTIONS_OFFSET = DHCP_COOKIE_OFFSET + 4;

  always_ff @ (posedge clk) begin
    if (fsm_rst) cur_tx <= tx_hdr;
    else begin
      case (byte_cnt) 
        (DHCP_HDR_LEN - 1)        : cur_tx <= tx_zero;
        (DHCP_COOKIE_OFFSET - 1)  : cur_tx <= tx_cookie;
        (DHCP_OPTIONS_OFFSET - 1) : cur_tx <= tx_opt;
        default:;
      endcase
    end
  end

  logic rst_tx, shift;
  // keep tx output logic reset while compling options
  always_ff @ (posedge clk) if (dhcp.val) rst_tx <= 1; else rst_tx <= 0;

  always_ff @ (posedge clk) if (udp.req) udp.rdy <= 0; else if (dhcp.val) udp.rdy <= 1;

  always_ff @ (posedge clk) if (fsm_rst) shift <= 0; else if (udp.req) shift <= 1;

  always_ff @ (posedge clk) if (fsm_rst) byte_cnt <= 0; else if (udp.strm.val) byte_cnt <= byte_cnt + 1;
  
  always_ff @ (posedge clk)  fsm_rst <= (rst || udp.strm.eof); 

  logic [3:0][7:0] cookie;
  
  logic [7:0] dat;

  always_ff @ (posedge clk) begin
    if (rst_tx) begin
      cookie  <= DHCP_COOKIE;
      hdr <= dhcp.hdr;
      opt <= {
        DHCP_OPT_MSG_TYPE,              // 1
        DHCP_OPT_MSG_TYPE_LEN,          // 2
        dhcp.opt_hdr.dhcp_opt_msg_type, // 3

        DHCP_OPT_REQ_IP,                // 4
        DHCP_OPT_REQ_IP_LEN,            // 5
        dhcp.opt_hdr.dhcp_opt_req_ip,   // 9
        
        DHCP_OPT_DHCP_CLI_ID,           // 10
        DHCP_OPT_DHCP_CLI_ID_LEN,       // 11
        8'h1,                           // 12
        MAC_ADDR,                       // 18
        
        DHCP_OPT_HOSTNAME,              // 19
        HOSTNAME_LEN,                   // 20
        HOSTNAME,                       // 20 + HOSTNAME_LEN
        
        DHCP_OPT_DOMAIN_NAME,           // 21 + HOSTNAME_LEN
        DOMAIN_NAME_LEN,                // 22 + HOSTNAME_LEN
        DOMAIN_NAME,                    // 22 + DOMAIN_NAME_LEN + HOSTNAME_LEN
        
        DHCP_OPT_FQDN,                  // 23 + DOMAIN_NAME_LEN + HOSTNAME_LEN
        FQDN_TOT_LEN,                   // 24 + DOMAIN_NAME_LEN + HOSTNAME_LEN
        DHCP_FQDN_FLAGS,                // 25 + DOMAIN_NAME_LEN + HOSTNAME_LEN
        DHCP_FQDN_RCODE1,               // 26 + DOMAIN_NAME_LEN + HOSTNAME_LEN
        DHCP_FQDN_RCODE1,               // 27 + DOMAIN_NAME_LEN + HOSTNAME_LEN
        FQDN,                           // 27 + FQDN_LEN + DOMAIN_NAME_LEN + HOSTNAME_LEN
        
        DHCP_OPT_END};                  // 28 + FQDN_LEN + DOMAIN_NAME_LEN + HOSTNAME_LEN
    end
    else if (shift) begin
      case (cur_tx)
        tx_hdr    : hdr    <= hdr    << $bits(byte);
        tx_cookie : cookie <= cookie << $bits(byte);
        tx_opt    : opt    <= opt    << $bits(byte);
        default   :;
      endcase
    end
  end

  logic sof, eof, val;
  always_comb begin
    case (cur_tx)
      tx_hdr    : udp.strm.dat = hdr[DHCP_HDR_LEN-1];
      tx_zero   : udp.strm.dat = 0;
      tx_cookie : udp.strm.dat = cookie[3];
      tx_opt    : udp.strm.dat = opt[OPT_REG_BYTES-1];
      default   : udp.strm.dat = 0;
    endcase
    udp.strm.val = val;
    udp.strm.sof = sof;
    udp.strm.eof = eof;
  end

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      val <= 0;
      sof <= 0;
      eof <= 0;
    end
    else begin
      if (udp.req) val <= 1; else if (eof) val <= 0;
      sof <= !val && udp.req;
      eof <= (byte_cnt == DHCP_HDR_TOT_LEN + OPT_REG_BYTES - 1);
    end
  end
  
  assign dhcp.done = udp.strm.eof;
  
endmodule : dhcp_vlg_tx
