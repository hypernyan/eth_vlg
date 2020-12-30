import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import eth_vlg_pkg::*;
import tcp_vlg_pkg::*;

interface ipv4
#( 
	parameter N = 1)
(
);
  logic [7:0] dat;
  logic       val;
  logic       sof;
  logic       eof;
  logic       err;
  logic       rdy;
  logic       req;
  ipv4_meta_t meta;

  modport in_tx  (input  dat, val, sof, eof, meta, rdy, output req); // used for transmitting ipv4 
  modport out_tx (output dat, val, sof, eof, meta, rdy, input  req); // used for transmitting ipv4 

  modport in_rx  (input  dat, val, sof, eof, err, meta); // used for receiving ipv4 
  modport out_rx (output dat, val, sof, eof, err, meta); // used for receiving ipv4 
endinterface

module ip_vlg_top #(
  parameter int                        N_TCP                = 1,
  parameter            [31:0]          MTU                  = 1400,
  parameter [N_TCP-1:0][31:0]          TCP_RETRANSMIT_TICKS = 1000000,
  parameter [N_TCP-1:0][31:0]          TCP_RETRANSMIT_TRIES = 5,
  parameter [N_TCP-1:0][31:0]          TCP_RAM_DEPTH        = 12,        
  parameter [N_TCP-1:0][31:0]          TCP_PACKET_DEPTH     = 8,     
  parameter [N_TCP-1:0][31:0]          TCP_WAIT_TICKS       = 100,
  parameter mac_addr_t                 MAC_ADDR             = 0,
  parameter int                        DOMAIN_NAME_LEN      = 5,
  parameter int                        HOSTNAME_LEN         = 8,
  parameter int                        FQDN_LEN             = 9,
  parameter [0:DOMAIN_NAME_LEN-1][7:0] DOMAIN_NAME          = "fpga0",  
  parameter [0:HOSTNAME_LEN-1]   [7:0] HOSTNAME             = "fpga_eth",  
  parameter [0:FQDN_LEN-1]       [7:0] FQDN                 = "fpga_host",  
  parameter int                        DHCP_TIMEOUT         = 1250000000,
  parameter bit                        DHCP_ENABLE          = 1,
  parameter bit                        IPV4_VERBOSE         = 0,
  parameter bit                        UDP_VERBOSE          = 0,
  parameter bit                        DHCP_VERBOSE         = 0,
  parameter bit                        TCP_VERBOSE          = 0
)                       
(
  input logic                    clk,
  input logic                    rst,
  mac.in_rx                      rx,
  mac.out_tx                     tx,
  input dev_t                    dev,
  // Connects to ARP table
  output ipv4_t                  arp_ipv4, // Requested IPv4 to ARP table
  output logic                   arp_req,  // Request valid
  input  mac_addr_t              arp_mac,  // MAC address response from ARP table for arp_ipv4
  input  logic                   arp_val,  // MAC address response valid
  input  logic                   arp_err,  // MAC entry not found or ARP request timeout
  // Raw TCP
  input  logic  [N_TCP-1:0][7:0] tcp_din,  // Transmitted TCP data
  input  logic  [N_TCP-1:0]      tcp_vin,  // Transmitted TCP data valid
  output logic  [N_TCP-1:0]      tcp_cts,  // TCP tx is clear to send
  input  logic  [N_TCP-1:0]      tcp_snd,  // Force send
  output logic  [N_TCP-1:0][7:0] tcp_dout, // Received TCP data
  output logic  [N_TCP-1:0]      tcp_vout, // Received TCP data valid
  // TCP control
  input  port_t [N_TCP-1:0]      port,      // Local port
  input  ipv4_t [N_TCP-1:0]      rem_ipv4,  // Remote IPv4 (not used for listen mode)
  input  port_t [N_TCP-1:0]      rem_port,  // Remote port (not used for listen mode)
  input  logic  [N_TCP-1:0]      connect,   // Connect to rem_ipv4 at rem_port
  output logic  [N_TCP-1:0]      connected, // Connection status
  input  logic  [N_TCP-1:0]      listen,    // Put the core to listen state
  // Core status
  output logic                   ready,          // Ready to connect
  output logic                   error,          // Error during configuration
  // DHCP related
  input  ipv4_t                  preferred_ipv4, // Try to aquire this IP
  input  logic                   dhcp_start,     // Initialize DHCP DORA
  output ipv4_t                  assigned_ipv4,  // Actually assigned IP to the device
  output logic                   dhcp_success,   // DHCP DORA was successfull. Assigned IP valid
  output logic                   dhcp_fail       // DHCP DORA timeout
);

  ipv4 ipv4_tx(.*);
  ipv4 ipv4_rx(.*);
  
  ipv4 icmp_ipv4_tx(.*);
  ipv4 udp_ipv4_tx(.*);
  
  udp udp_tx(.*);
  udp udp_rx(.*);
  
  //////////
  // IPv4 //
  //////////
  ipv4_vlg #(
    .VERBOSE (IPV4_VERBOSE)
  ) ipv4_vlg_inst (
    .clk      (clk),
    .rst      (rst),
  
    .mac_rx   (rx),
    .mac_tx   (tx),
    .dev      (dev),
   
    .arp_ipv4 (arp_ipv4),
    .arp_req  (arp_req),
    .arp_mac  (arp_mac),
    .arp_val  (arp_val),
    .arp_err  (arp_err),
    .ipv4_tx  (ipv4_tx),
    .ipv4_rx  (ipv4_rx)
  );
  
  icmp_vlg icmp_vlg_inst (
    .clk  (clk),
    .rst  (rst),
    .rx   (ipv4_rx),
    .dev  (dev),
    .tx   (icmp_ipv4_tx)
  );

  ///////////////////////
  // UDP for DHCP only //
  ///////////////////////
  udp_vlg #(
    .VERBOSE (UDP_VERBOSE)
  ) udp_vlg_inst (
    .clk    (clk),
    .rst    (rst),
    .rx     (ipv4_rx),
    .tx     (udp_ipv4_tx),
    .udp_tx (udp_tx),
    .udp_rx (udp_rx),
    .dev    (dev)
  );
  
  //////////
  // DHCP //
  //////////
  dhcp_vlg #(
    .MAC_ADDR        (MAC_ADDR),
    .DOMAIN_NAME_LEN (DOMAIN_NAME_LEN),
    .HOSTNAME_LEN    (HOSTNAME_LEN),
    .FQDN_LEN        (FQDN_LEN),
    .DOMAIN_NAME     (DOMAIN_NAME),
    .HOSTNAME        (HOSTNAME),
    .FQDN            (FQDN),
    .TIMEOUT         (DHCP_TIMEOUT),
    .ENABLE          (DHCP_ENABLE),
    .VERBOSE         (DHCP_VERBOSE)
  ) dhcp_vlg_inst (
    .clk            (clk),
    .rst            (rst),
    .rx             (udp_rx),
    .tx             (udp_tx),
    //.dev          (dev),
    // Core status
    .ready          (ready),
    .error          (error),
    // DHCP related
    .preferred_ipv4 (preferred_ipv4),
    .start          (dhcp_start),
    .assigned_ipv4  (assigned_ipv4),
    .success        (dhcp_success),
    .fail           (dhcp_fail)
  );


  logic       [N_TCP-1:0] [7:0] tcp_ipv4_tx_dat;  
  logic       [N_TCP-1:0]       tcp_ipv4_tx_val;  
  logic       [N_TCP-1:0]       tcp_ipv4_tx_sof;  
  logic       [N_TCP-1:0]       tcp_ipv4_tx_eof;  
  logic       [N_TCP-1:0]       tcp_ipv4_tx_rdy;  
  logic       [N_TCP-1:0]       tcp_ipv4_tx_req;  
  ipv4_meta_t [N_TCP-1:0]       tcp_ipv4_tx_meta;

  genvar i;
  
  generate
    for (i = 0; i < N_TCP; i = i + 1) begin : gen
      ipv4 tcp_ipv4_tx(.*);
      ipv4 tcp_ipv4_rx(.*);

    end
  endgenerate
  
  generate
    for (i = 0; i < N_TCP; i = i + 1) begin : gen_tcp
      tcp_vlg #(
        .MTU              (MTU),
        .MAX_PAYLOAD_LEN  (MTU - 120),
        .RETRANSMIT_TICKS (TCP_RETRANSMIT_TICKS[i]),
        .RETRANSMIT_TRIES (TCP_RETRANSMIT_TRIES[i]),
        .RAM_DEPTH        (TCP_RAM_DEPTH[i]),
        .PACKET_DEPTH     (TCP_PACKET_DEPTH[i]),
        .WAIT_TICKS       (TCP_WAIT_TICKS[i]),
        .VERBOSE          (TCP_VERBOSE)
      ) tcp_vlg_inst (
        .clk       (clk),
        .rst       (rst),
        .dev       (dev),
        .port      (port[i]),
        .rx        (gen[i].tcp_ipv4_rx),
        .tx        (gen[i].tcp_ipv4_tx),
        .din       (tcp_din[i]),
        .vin       (tcp_vin[i]),
        .cts       (tcp_cts[i]),
        .snd       (tcp_snd[i]),
  
        .dout      (tcp_dout[i]),
        .vout      (tcp_vout[i]),
  
        .connected (connected[i]),
        .connect   (connect  [i]),
        .listen    (listen   [i]),
        .rem_ipv4  (rem_ipv4 [i]),
        .rem_port  (rem_port [i])
      );
      // rx connections

      assign gen[i].tcp_ipv4_rx.dat  = ipv4_rx.dat;
      assign gen[i].tcp_ipv4_rx.val  = ipv4_rx.val;
      assign gen[i].tcp_ipv4_rx.sof  = ipv4_rx.sof;
      assign gen[i].tcp_ipv4_rx.eof  = ipv4_rx.eof;
      assign gen[i].tcp_ipv4_rx.err  = ipv4_rx.err;
      assign gen[i].tcp_ipv4_rx.meta = ipv4_rx.meta;
      // tx connections
      // tcp -> ipv4
      assign tcp_ipv4_tx_dat[i]  = gen[i].tcp_ipv4_tx.dat;
      assign tcp_ipv4_tx_val[i]  = gen[i].tcp_ipv4_tx.val;
      assign tcp_ipv4_tx_sof[i]  = gen[i].tcp_ipv4_tx.sof;
      assign tcp_ipv4_tx_eof[i]  = gen[i].tcp_ipv4_tx.eof;
      assign tcp_ipv4_tx_rdy[i]  = gen[i].tcp_ipv4_tx.rdy;
      assign tcp_ipv4_tx_meta[i] = gen[i].tcp_ipv4_tx.meta;
      // ipv4 -> tcp
      assign gen[i].tcp_ipv4_tx.req  = tcp_ipv4_tx_req[i];
      
    end
  endgenerate

  // Common interfaces to IPv4 TX multiplexer (ipv4_vlg_tx_mux)
  eth_vlg_tx_mux #(
    .N (N_TCP + 2),
    .W ($bits(ipv4_meta_t))
  ) eth_vlg_tx_mux_isnt (
    .clk (clk),
    .rst (rst),
    // UDP, TCP and ICMP interface
    // IPv4 interface
    .dat      ({tcp_ipv4_tx_dat,  udp_ipv4_tx.dat, icmp_ipv4_tx.dat}),       
    .val      ({tcp_ipv4_tx_val,  udp_ipv4_tx.val, icmp_ipv4_tx.val}),       
    .sof      ({tcp_ipv4_tx_sof,  udp_ipv4_tx.sof, icmp_ipv4_tx.sof}),       
    .eof      ({tcp_ipv4_tx_eof,  udp_ipv4_tx.eof, icmp_ipv4_tx.eof}),       
    .rdy      ({tcp_ipv4_tx_rdy,  udp_ipv4_tx.rdy, icmp_ipv4_tx.rdy}),       
    .req      ({tcp_ipv4_tx_req,  udp_ipv4_tx.req, icmp_ipv4_tx.req}),       
    .meta     ({tcp_ipv4_tx_meta, udp_ipv4_tx.meta, icmp_ipv4_tx.meta}),
    
    .dat_mux  (ipv4_tx.dat),
    .val_mux  (ipv4_tx.val),
    .sof_mux  (ipv4_tx.sof),
    .eof_mux  (ipv4_tx.eof),
    .rdy_mux  (ipv4_tx.rdy),
    .req_mux  (ipv4_tx.req),
    .meta_mux (ipv4_tx.meta)
  );
endmodule

module ipv4_vlg #(
  parameter bit VERBOSE = 1
)
(
  input logic clk,
  input logic rst,

  mac.in_rx  mac_rx,
  mac.out_tx mac_tx,
  input  dev_t dev,

// ARP request/response
  output ipv4_t    arp_ipv4,
  output logic     arp_req,
  input mac_addr_t arp_mac,
  input logic      arp_val,
  input logic      arp_err,

  ipv4.in_tx  ipv4_tx,
  ipv4.out_rx ipv4_rx
);

  ipv4_vlg_rx #(
    .VERBOSE (VERBOSE)
  )
  ipv4_vlg_rx_inst (
    .clk  (clk),
    .rst  (rst),
    .mac  (mac_rx),
    .ipv4 (ipv4_rx),
    .dev  (dev)
  );
  
  ipv4_vlg_tx #(
    .VERBOSE (VERBOSE)
  ) ipv4_vlg_tx_inst (
    .clk      (clk),
    .rst      (rst),
    .mac      (mac_tx),
    .ipv4     (ipv4_tx),
    .dev      (dev),
    .arp_ipv4 (arp_ipv4),
    .arp_req  (arp_req),
    .arp_mac  (arp_mac),
    .arp_val  (arp_val),
    .arp_err  (arp_err)
  );

endmodule : ipv4_vlg

module ipv4_vlg_rx #(
  parameter bit VERBOSE = 1
)
(
  input logic clk,
  input logic rst,
  mac.in_rx   mac,
  ipv4.out_rx ipv4,
  input dev_t dev
);

  logic [18:0] chsum;
  logic [15:0] chsum_rec;
  logic [15:0] chsum_calc;
  logic [7:0]  chsum_hi;
  logic [2:0]  chsum_carry;
  logic        chsum_ctrl;
  logic        chsum_ok;
  
  assign chsum_carry = chsum[18:16];
  assign chsum_calc  = chsum[15:0] + chsum_carry;
  
  logic [15:0] byte_cnt;
  logic fsm_rst, receiving, hdr_done;
  
  logic [IPV4_HDR_LEN-1:0][7:0] hdr;
  
  // Handle incoming packets, check for errors
  logic [5:0] ihl_bytes;
  always @ (posedge clk) begin
    if (fsm_rst || rst) begin
      receiving     <= 0;
      hdr_done      <= 0;
      chsum         <= 0;
      chsum_hi      <= 0;
      byte_cnt      <= 0;
      ipv4.dat      <= 0;
      ipv4.sof      <= 0;
      ipv4.eof      <= 0;
      ipv4.meta.ipv4_hdr <= 0;
      ipv4.meta.mac_hdr <= 0;
    end
    else begin
      hdr[IPV4_HDR_LEN-1:1] <= hdr[IPV4_HDR_LEN-2:0];
      if (byte_cnt == IPV4_HDR_LEN-2) begin
        ipv4.meta.ipv4_hdr[159:0] <= hdr[19:0];
        ipv4.meta.pl_len <= hdr[17:16] - 20;
      end
      if (mac.sof && (mac.meta.hdr.ethertype == eth_vlg_pkg::IPv4)) begin
        ipv4.meta.mac_hdr <= mac.meta.hdr;
        ihl_bytes <= {mac.dat[3:0], 2'b00};
        receiving <= 1;
      end
      if (receiving && (byte_cnt == (ihl_bytes - 1))) hdr_done <= 1;
      if (mac.val) begin
        if (byte_cnt[0]) chsum <= chsum + {chsum_hi, mac.dat};
        if (!byte_cnt[0]) chsum_hi <= mac.dat;
        if (receiving) byte_cnt <= byte_cnt + 1;
      end
      ipv4.dat <= mac.dat;
      ipv4.sof <= receiving && (byte_cnt == IPV4_HDR_LEN - 1);
      ipv4.eof <= hdr_done && (byte_cnt == ipv4.meta.ipv4_hdr.length - 2);
      if (ipv4.eof) begin
        if (VERBOSE) $display("[DUT]<- %d.%d.%d.%d: IPv4 from %d.%d.%d.%d",
          dev.ipv4_addr[3],
          dev.ipv4_addr[2],
          dev.ipv4_addr[1],
          dev.ipv4_addr[0],
          ipv4.meta.ipv4_hdr.src_ip[3],
          ipv4.meta.ipv4_hdr.src_ip[2],
          ipv4.meta.ipv4_hdr.src_ip[1],
          ipv4.meta.ipv4_hdr.src_ip[0]
        );
      end
    end
  end
  
  assign ipv4.val   = (hdr_done && (ipv4.meta.ipv4_hdr.dst_ip == dev.ipv4_addr || ipv4.meta.ipv4_hdr.dst_ip == IPV4_BROADCAST));
  assign fsm_rst  = (ipv4.eof || ipv4.err);
  assign hdr[0] = mac.dat;
  
  // Calculate chsum
  always @ (posedge clk) begin
    if (fsm_rst) begin
      chsum_ok <= 0;
    end
    else begin
      //if (chsum_ctrl && (chsum_calc == '1)) begin
      if (chsum_ctrl) begin
        chsum_ok <= 1;
      end
      else chsum_ok <= 0;
      if (chsum_ctrl && (chsum_calc != '1)) begin
        //if (fsm == ipv4_payload_s && byte_cnt == ipv4.ipv4_hdr.ihl*4) $display("IPv4 core: Bad header chsum.");
      end
    end
  end

endmodule : ipv4_vlg_rx

module ipv4_vlg_tx #(
  parameter bit VERBOSE = 1
)
(
  input  logic  clk,
  input  logic  rst,
  mac.out_tx    mac,
  ipv4.in_tx    ipv4,
  input  dev_t  dev,
  // ARP table request/response
  output ipv4_t    arp_ipv4,
  input mac_addr_t arp_mac,
  output logic     arp_req,
  input logic      arp_val,
  input logic      arp_err
);

  parameter int CHECKSUM_CALC_POW_WIDTH = 4; // 

  logic fsm_rst;
  logic hdr_done;
  
  logic [IPV4_HDR_LEN-1:0][7:0] hdr;
  logic [IPV4_HDR_LEN-1:0][7:0] hdr_calc;
  logic [15:0] byte_cnt, length;
  
  
  logic [15:0] chsum;
  logic [19:0] chsum_carry;
  logic [3:0] calc_byte_cnt;
  logic calc;
  logic calc_done;
  logic [7:0] hdr_tx;
  
  // length_t length;
  logic active;
  logic tx_sof_reg;
  logic tx_val_reg;
  
  ipv4_meta_t cur_meta;

  enum logic [2:0] {idle_s, prep_s, active_s} fsm;
  logic [$clog2(CHECKSUM_CALC_POW_WIDTH+1)-1:0] calc_ctr;
  always @ (posedge clk) begin
    if (fsm_rst) begin
      fsm           <= idle_s;
      calc          <= 0;
      hdr_calc      <= 0;
      chsum_carry   <= 0;
      calc_byte_cnt <= 0;
      hdr_done      <= 0;
     // calc_done     <= 0;
      byte_cnt      <= 0;
      ipv4.req      <= 0;
      mac.val       <= 0;
      mac.sof       <= 0;
      mac.eof       <= 0;
      mac.rdy       <= 0;
      mac.meta      <= 0; 
      arp_ipv4      <= 0;
      hdr           <= 0;
      length        <= 0;
      active        <= 0;
      tx_sof_reg    <= 0;
      tx_val_reg    <= 0;
      arp_req       <= 0;
      calc_ctr      <= 0;
      calc_done     <= 0;
      cur_meta      <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (ipv4.rdy) begin
            fsm <= prep_s;
            mac.meta.len <= ipv4.meta.ipv4_hdr.length;            
            hdr[19]      <= {ipv4.meta.ipv4_hdr.ver, ipv4.meta.ipv4_hdr.ihl};
            hdr[18]      <= ipv4.meta.ipv4_hdr.qos;                           
            hdr[17:16]   <= ipv4.meta.ipv4_hdr.length;
            hdr[15:14]   <= ipv4.meta.ipv4_hdr.id;
            hdr[13][7]   <= 0;
            hdr[13][6]   <= ipv4.meta.ipv4_hdr.df;
            hdr[13][5]   <= ipv4.meta.ipv4_hdr.mf;
            hdr[13][4]   <= 0;
            hdr[13][3:0] <= ipv4.meta.ipv4_hdr.fo[11:8];
            hdr[12]      <= ipv4.meta.ipv4_hdr.fo[7:0];
            hdr[11]      <= ipv4.meta.ipv4_hdr.ttl;
            hdr[10]      <= ipv4.meta.ipv4_hdr.proto;
            hdr[9:8]     <= 0;
            hdr[7:4]     <= ipv4.meta.ipv4_hdr.src_ip;
            hdr[3:0]     <= ipv4.meta.ipv4_hdr.dst_ip;

            length <= ipv4.meta.ipv4_hdr.length;
            cur_meta <= ipv4.meta;
          end
        end
        prep_s : begin
          calc_ctr <= calc_ctr + 1;
          if (calc_ctr == CHECKSUM_CALC_POW_WIDTH - 1) begin
      //      $display("from ipv4 mac %h", cur_meta.mac_hdr.dst_mac);
      //      $display("from ipv4 mac known%h", cur_meta.mac_known);
            calc_done <= 1;
          end
          mac.meta.hdr.src_mac   <= dev.mac_addr;
          mac.meta.hdr.ethertype <= eth_vlg_pkg::IPv4;
          if (!cur_meta.mac_known) arp_req <= 1;
          arp_ipv4 <= cur_meta.ipv4_hdr.dst_ip; // Request MAC for destination IP
          if (calc_done && (cur_meta.mac_known || arp_val)) begin
            mac.meta.hdr.dst_mac   <= cur_meta.mac_known ? cur_meta.mac_hdr.dst_mac : arp_mac; // request dst MAC from ARP table if unknown
            mac.rdy <= 1;
            arp_req <= 0;
          end
        //  else if (arp_err) 
          if (mac.req) fsm <= active_s;
        end
        active_s : begin
          arp_req <= 0;
          mac.sof <= (byte_cnt == 0);
          mac.eof <= ipv4.eof;
          mac.dat <= (hdr_done) ? ipv4.dat : hdr[IPV4_HDR_LEN-1];
          if (byte_cnt == 0) mac.val <= 1;
          else if (mac.eof) mac.val <= 0;
          hdr[IPV4_HDR_LEN-1:1] <= hdr[IPV4_HDR_LEN-2:0];
         // ipv4.done <= active && ((byte_cnt == length) || arp_err); 
          if (byte_cnt == IPV4_HDR_LEN-4) ipv4.req <= 1; // Read out data from buffer. Tx mux needs 4 ticks to start output
          if (byte_cnt == IPV4_HDR_LEN-1) hdr_done <= 1; // Done transmitting header, switch to buffer output
          byte_cnt <= byte_cnt + 1;
        end
      endcase
    end
  end
  
  assign chsum = ~(chsum_carry[19:16] + chsum_carry[15:0]); // Calculate actual chsum  
  always @ (posedge clk) if (rst) fsm_rst <= 1; else fsm_rst <= (ipv4.eof || arp_err);

  sum #(
    .W ($bits(byte)*2),
    .N (CHECKSUM_CALC_POW_WIDTH)
  ) sum_inst (
    .clk (clk),
    .in  ({{{(16*(2**4)-$bits(hdr))}{1'b0}}, hdr}),
    .res (chsum_carry)
  );

endmodule : ipv4_vlg_tx
