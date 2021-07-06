
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
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME     = "nya", 
  parameter [0:HOSTNAME_LEN-1][7:0]    HOSTNAME        = "localnya",
  parameter [0:FQDN_LEN-1][7:0]        FQDN            = "www.nya.com"
)
(
  input logic clk,
  input logic rst,
  udp.out_tx  udp,
  dhcp.in     dhcp
);
  logic fsm_rst, shift_opt;
  logic opt_rdy;
  
  logic [dhcp_vlg_pkg::OPT_NUM_TX-1:0][dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_hdr_proto;
  logic [0:dhcp_vlg_pkg::OPT_NUM_TX-1][dhcp_vlg_pkg::OPT_LEN-1:0][7:0] opt_hdr;
  logic [dhcp_vlg_pkg::OPT_NUM_TX-1:0] dhcp_opt_pres;
  
  logic [$clog2(dhcp_vlg_pkg::OPT_NUM_TX+1)-1:0] opt_cnt;
  logic [$clog2(dhcp_vlg_pkg::OPT_TOT_LEN_TX+1)-1:0] opt_len;
  
  logic tx_en;
  logic [15:0] byte_cnt;
  logic [0:DHCP_HDR_LEN+dhcp_vlg_pkg::OPT_TOT_LEN_TX-1][7:0] hdr;
  logic rst_reg;
  
  logic [31:0] ipv4_id_prng;
  
  // logic resets itself after transmission
  assign fsm_rst = (rst || rst_reg); 

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
          {DHCP_OPT_MSG_TYPE,      DHCP_OPT_MSG_TYPE_LEN,                 dhcp.opt_hdr.dhcp_opt_msg_type,   {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_MSG_TYPE_LEN    - 2){DHCP_OPT_PAD}}},
          {DHCP_OPT_REQ_IP,        DHCP_OPT_REQ_IP_LEN,                   dhcp.opt_hdr.dhcp_opt_req_ip,     {(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_REQ_IP_LEN      - 2){DHCP_OPT_PAD}}},               
          {DHCP_OPT_DHCP_CLI_ID,   DHCP_OPT_DHCP_CLI_ID_LEN,              dhcp.opt_hdr.dhcp_opt_dhcp_cli_id,{(dhcp_vlg_pkg::OPT_LEN-DHCP_OPT_DHCP_CLI_ID_LEN - 2){DHCP_OPT_PAD}}},           
          {DHCP_OPT_HOSTNAME,      dhcp.opt_len.dhcp_opt_hostname_len,    HOSTNAME,                         {(dhcp_vlg_pkg::OPT_LEN-HOSTNAME_LEN             - 2){DHCP_OPT_PAD}}},  
          {DHCP_OPT_DOMAIN_NAME,   dhcp.opt_len.dhcp_opt_domain_name_len, DOMAIN_NAME,                      {(dhcp_vlg_pkg::OPT_LEN-DOMAIN_NAME_LEN          - 2){DHCP_OPT_PAD}}},                  
          {DHCP_OPT_FQDN,          dhcp.opt_len.dhcp_opt_fqdn_len,        dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_flags, dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_rcode1, dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_rcode2, FQDN, {(dhcp_vlg_pkg::OPT_LEN-FQDN_LEN/*extra bytes*/  - 5){DHCP_OPT_PAD}}},   
          {{(dhcp_vlg_pkg::OPT_LEN-1){DHCP_OPT_PAD}}, DHCP_OPT_END}
        };
        dhcp_opt_pres <= dhcp.opt_pres;
      end
      else if (shift_opt) begin // create valid options to concat them with dhcp header      
        opt_cnt <= opt_cnt + 1;
        dhcp_opt_pres[dhcp_vlg_pkg::OPT_NUM_TX-2:0] <= dhcp_opt_pres[dhcp_vlg_pkg::OPT_NUM_TX-1:1];
        opt_hdr_proto[dhcp_vlg_pkg::OPT_NUM_TX-2:0] <= opt_hdr_proto[dhcp_vlg_pkg::OPT_NUM_TX-1:1];
        if (dhcp_opt_pres[0]) begin // Shift by 32 bits
          opt_len <= opt_len + dhcp_vlg_pkg::OPT_LEN;
          opt_hdr[1:dhcp_vlg_pkg::OPT_NUM_TX-1] <= opt_hdr[0:dhcp_vlg_pkg::OPT_NUM_TX-2];
          opt_hdr[0] <= opt_hdr_proto[0];
        end
        if (opt_cnt == dhcp_vlg_pkg::OPT_NUM_TX-1) begin
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
      rst_reg      <= 0;
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
      if (dhcp.val) hdr[0:DHCP_HDR_LEN-1] <= dhcp.hdr;
      else if (udp.req) begin
        udp.strm.val <= 1;
        udp.strm.sof <= (byte_cnt == 0);
        hdr[0:dhcp_vlg_pkg::HDR_TOT_LEN_TX-2] <= hdr[1:dhcp_vlg_pkg::HDR_TOT_LEN_TX-1];
        byte_cnt <= byte_cnt + 1;
        udp.strm.dat <= hdr[0];
        if (byte_cnt == DHCP_HDR_LEN + opt_len - 1) begin // 1 last byte for end option
          rst_reg <= 1;
          udp.strm.eof <= 1;
        end
      end
      else if (opt_rdy) begin
        udp.rdy <= 1;
        if (!udp.rdy) $display("udp.meta.udp_hdr.length %d", DHCP_HDR_LEN + opt_len);
        hdr[DHCP_HDR_LEN:dhcp_vlg_pkg::HDR_TOT_LEN_TX-1] <= opt_hdr;
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
