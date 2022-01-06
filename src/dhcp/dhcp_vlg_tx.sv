
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
  parameter [FQDN_LEN-1:0][7:0]        FQDN            = "www.nya.com"
)
(
  input logic    clk,
  input logic    rst,
  udp_ifc.out_tx udp,
  dhcp_ifc.in    dhcp
);

  logic fsm_rst, shift_opt;
  logic opt_rdy;
  
  logic [OPT_NUM_TX-1:0][OPT_LEN-1:0][7:0] opt_hdr_proto;
  logic [OPT_NUM_TX-1:0][OPT_LEN-1:0][7:0] opt_hdr;
  logic [OPT_NUM_TX-1:0] dhcp_opt_pres;
  
  logic [$clog2(OPT_NUM_TX+1)-1:0] opt_cnt;
  logic [$clog2(OPT_TOT_LEN_TX+1)-1:0] opt_len;
  
  logic tx_en;
  logic [15:0] byte_cnt;
  logic [DHCP_HDR_LEN+OPT_TOT_LEN_TX-1:0][7:0] hdr;
  
  logic [31:0] ipv4_id_prng;
  
  // logic resets itself after transmission
  assign fsm_rst = (rst || dhcp.done); 

  ///////////////////////
  // Options assembler //
  ///////////////////////
  // Every option has length of OPT_LEN
  // And is padded by zeros if necessary
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      opt_cnt       <= 0;
      opt_rdy       <= 0;
      shift_opt     <= 0;
      opt_len       <= 0;
    end
    else begin
      if (dhcp.val) begin // transmit starts here
        opt_len   <= 0;
        shift_opt <= 1; // After options and header are set, compose a valid option header
        opt_hdr_proto <= {
          {DHCP_OPT_MSG_TYPE,      DHCP_OPT_MSG_TYPE_LEN,                 dhcp.opt_hdr.dhcp_opt_msg_type,   {(OPT_LEN-DHCP_OPT_MSG_TYPE_LEN    - 2){DHCP_OPT_PAD}}},
          {DHCP_OPT_REQ_IP,        DHCP_OPT_REQ_IP_LEN,                   dhcp.opt_hdr.dhcp_opt_req_ip,     {(OPT_LEN-DHCP_OPT_REQ_IP_LEN      - 2){DHCP_OPT_PAD}}},               
          {DHCP_OPT_DHCP_CLI_ID,   DHCP_OPT_DHCP_CLI_ID_LEN,              dhcp.opt_hdr.dhcp_opt_dhcp_cli_id,{(OPT_LEN-DHCP_OPT_DHCP_CLI_ID_LEN - 2){DHCP_OPT_PAD}}},           
          {DHCP_OPT_HOSTNAME,      dhcp.opt_len.dhcp_opt_hostname_len,    HOSTNAME,                         {(OPT_LEN-HOSTNAME_LEN             - 2){DHCP_OPT_PAD}}},  
          {DHCP_OPT_DOMAIN_NAME,   dhcp.opt_len.dhcp_opt_domain_name_len, DOMAIN_NAME,                      {(OPT_LEN-DOMAIN_NAME_LEN          - 2){DHCP_OPT_PAD}}},                  
          {DHCP_OPT_FQDN,          dhcp.opt_len.dhcp_opt_fqdn_len,        dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_flags, dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_rcode1, dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_rcode2, FQDN, {(OPT_LEN-FQDN_LEN/*extra bytes*/  - 5){DHCP_OPT_PAD}}},   
          {{(OPT_LEN-1){DHCP_OPT_PAD}}, DHCP_OPT_END}
        };
        dhcp_opt_pres <= dhcp.opt_pres;
      end
      else if (shift_opt) begin // create valid options to concat them with dhcp header      
        opt_cnt <= opt_cnt + 1;
        dhcp_opt_pres[OPT_NUM_TX-2:0] <= dhcp_opt_pres[OPT_NUM_TX-1:1];
        opt_hdr_proto[OPT_NUM_TX-2:0] <= opt_hdr_proto[OPT_NUM_TX-1:1];
        if (dhcp_opt_pres[0]) begin // Shift by 32 bits
          opt_len <= opt_len + OPT_LEN;
          opt_hdr <= {opt_hdr_proto[0], opt_hdr[OPT_NUM_TX-1:1]};
        end
        if (opt_cnt == OPT_NUM_TX-1) begin
          opt_rdy   <= 1;
          shift_opt <= 0;
        end
      end
    end
  end
  
  //////////////////////
  // Transmit control //
  //////////////////////
  /*
  prng prng_ipv4_id_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (ipv4_id_prng)
  );
  */
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      dhcp.done      <= 0;
      tx_en        <= 0;
      byte_cnt     <= 0;
      udp.rdy      <= 0;
      udp.strm.sof <= 0;
      udp.strm.val <= 0;
      udp.strm.dat <= 0;
      udp.strm.eof <= 0;
      udp.meta     <= 0;
      hdr          <= 0;
    end
    else begin
      if (dhcp.val) hdr[HDR_TOT_LEN_TX-1-:DHCP_HDR_LEN] <= dhcp.hdr;
      else if (udp.req) begin
        udp.strm.val <= 1;
        udp.strm.sof <= (byte_cnt == 0);
        hdr[HDR_TOT_LEN_TX-1:1] <= hdr[HDR_TOT_LEN_TX-1:0];
        byte_cnt <= byte_cnt + 1;
        udp.strm.dat <= hdr[HDR_TOT_LEN_TX-1];
        if (byte_cnt == DHCP_HDR_LEN + opt_len - 1) begin // 1 last byte for end option
          dhcp.done <= 1;
          udp.strm.eof <= 1;
        end
      end
      else if (opt_rdy) begin
        udp.rdy <= 1;
        hdr[OPT_TOT_LEN_TX-1:0] <= opt_hdr;
        udp.meta.udp_hdr.src_port <= DHCP_CLI_PORT;
        udp.meta.udp_hdr.dst_port <= DHCP_SRV_PORT;
        udp.meta.udp_hdr.length   <= DHCP_HDR_LEN + udp_vlg_pkg::UDP_HDR_LEN + opt_len;
        udp.meta.udp_hdr.cks      <= 0; // checksum skipped
        udp.meta.ipv4_hdr.src_ip  <= dhcp.src_ip;
        udp.meta.ipv4_hdr.dst_ip  <= dhcp.dst_ip;
        udp.meta.ipv4_hdr.id      <= dhcp.ipv4_id;
        udp.meta.mac_known        <= 1;
        udp.meta.mac_hdr.dst_mac  <= mac_vlg_pkg::MAC_BROADCAST;
      end
    end
  end
endmodule : dhcp_vlg_tx
