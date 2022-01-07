
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
  
  logic [DHCP_HDR_LEN-1:0]           [7:0] hdr;
  logic [OPT_NUM_TX-1:0][OPT_LEN-1:0][7:0] opt_proto; // prototype contatining all possible options
  logic [OPT_NUM_TX-1:0][OPT_LEN-1:0][7:0] opt;       // composed options
  logic [OPT_TOT_LEN_TX-1:0]         [7:0] opt_reg;   // shiftreg for transmission
  logic [OPT_NUM_TX-1:0]                   opt_pres;  // shiftreg used to compose options from prototype 
  
  logic [$clog2(OPT_NUM_TX    +1)-1:0] opt_cnt;
  logic [$clog2(OPT_TOT_LEN_TX+1)-1:0] opt_len;
  
  logic tx_en;
  logic [$clog2(DHCP_HDR_TOT_LEN+OPT_LEN*OPT_NUM):0] byte_cnt;
  
  
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
        opt_proto <= {
          {DHCP_OPT_MSG_TYPE,    DHCP_OPT_MSG_TYPE_LEN,                 dhcp.opt_hdr.dhcp_opt_msg_type,   {(OPT_LEN-DHCP_OPT_MSG_TYPE_LEN    - 2){DHCP_OPT_PAD}}},
          {DHCP_OPT_REQ_IP,      DHCP_OPT_REQ_IP_LEN,                   dhcp.opt_hdr.dhcp_opt_req_ip,     {(OPT_LEN-DHCP_OPT_REQ_IP_LEN      - 2){DHCP_OPT_PAD}}},               
          {DHCP_OPT_DHCP_CLI_ID, DHCP_OPT_DHCP_CLI_ID_LEN,              dhcp.opt_hdr.dhcp_opt_dhcp_cli_id,{(OPT_LEN-DHCP_OPT_DHCP_CLI_ID_LEN - 2){DHCP_OPT_PAD}}},           
          {DHCP_OPT_HOSTNAME,    dhcp.opt_len.dhcp_opt_hostname_len,    HOSTNAME,                     {(OPT_LEN-HOSTNAME_LEN             - 2){DHCP_OPT_PAD}}},  
          {DHCP_OPT_DOMAIN_NAME, dhcp.opt_len.dhcp_opt_domain_name_len, DOMAIN_NAME,                  {(OPT_LEN-DOMAIN_NAME_LEN          - 2){DHCP_OPT_PAD}}},                  
          {DHCP_OPT_FQDN,        dhcp.opt_len.dhcp_opt_fqdn_len,        dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_flags, dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_rcode1, dhcp.opt_hdr.dhcp_opt_fqdn.fqdn_rcode2, FQDN, {(OPT_LEN-FQDN_LEN/*extra bytes*/  - 5){DHCP_OPT_PAD}}},   
          {{(OPT_LEN-1){DHCP_OPT_PAD}}, DHCP_OPT_END}
        };
        opt_pres <= dhcp.opt_pres;
      end
      else if (shift_opt) begin // create valid options to concat them with dhcp header      
        opt_cnt <= opt_cnt + 1;
        opt_pres[OPT_NUM_TX-2:0] <= opt_pres[OPT_NUM_TX-1:1];
        opt_proto[OPT_NUM_TX-2:0] <= opt_proto[OPT_NUM_TX-1:1];
        if (opt_pres[0]) begin // Shift by 32 bits
          opt_len <= opt_len + OPT_LEN;
          opt <= {opt_proto[0], opt[OPT_NUM_TX-1:1]};
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
  logic [31:0] ipv4_id_prng;

  prng prng_ipv4_id_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (ipv4_id_prng)
  );
  */

  logic cookie_en;
  logic cookie_done;
  logic hdr_done;
  logic [3:0][7:0] cookie;
  
  always_ff @ (posedge clk) begin
    udp.meta.udp_hdr.src_port <= DHCP_CLI_PORT;
    udp.meta.udp_hdr.dst_port <= DHCP_SRV_PORT;
    udp.meta.udp_hdr.cks      <= 0; // checksum skipped
    udp.meta.udp_hdr.length   <= DHCP_HDR_TOT_LEN + udp_vlg_pkg::UDP_HDR_LEN + opt_len;
    udp.meta.mac_known        <= 1;
    udp.meta.mac_hdr.dst_mac  <= mac_vlg_pkg::MAC_BROADCAST;
    udp.meta.ipv4_hdr.src_ip  <= dhcp.src_ip;
    udp.meta.ipv4_hdr.dst_ip  <= dhcp.dst_ip;
    udp.meta.ipv4_hdr.id      <= dhcp.ipv4_id;
  end

  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      hdr_done     <= 0;
      cookie_en    <= 0;
      cookie_done  <= 0;
    end
    else begin
      if (byte_cnt == DHCP_HDR_LEN - 1)       hdr_done <= 1;
      if (byte_cnt == DHCP_COOKIE_OFFSET - 1) cookie_en <= 1;
      if (byte_cnt == DHCP_HDR_TOT_LEN - 1)   cookie_done <= 1;
    end
  end

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
      hdr          <= 0;
    end
    else begin
      if (dhcp.val) hdr[DHCP_HDR_LEN-1:0] <= dhcp.hdr;
      else if (udp.req) begin
        udp.strm.val <= 1;
        udp.strm.sof <= (byte_cnt == 0);
        hdr[DHCP_HDR_LEN-1:1] <= hdr[DHCP_HDR_LEN-2:0];
        if (cookie_en) cookie[3:1] <= cookie[2:0]; else cookie <= DHCP_COOKIE;
        byte_cnt <= byte_cnt + 1;
        // transmit header, then replace sname and fname with 0s and lastly append cookie
        udp.strm.dat <= (hdr_done) ? (cookie_en) ? (cookie_done) ? opt_reg[OPT_TOT_LEN_TX-1] : cookie[3] : 8'h00 : hdr[DHCP_HDR_LEN-1];
        if (byte_cnt == DHCP_HDR_TOT_LEN + opt_len - 1) begin // frame sent
          dhcp.done <= 1;
          udp.strm.eof <= 1;
        end
      end
      if (cookie_done) opt_reg[OPT_TOT_LEN_TX-1:1] <= opt_reg[OPT_TOT_LEN_TX-2:0];
      else if (opt_rdy) begin // after options were assembled in order...
        udp.rdy <= 1;   // indicate UDP that fame is ready
        opt_reg <= opt; // and latch the composed options to shiftreg
      end
    end
  end


endmodule : dhcp_vlg_tx
