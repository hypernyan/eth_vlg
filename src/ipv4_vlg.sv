import ip_vlg_pkg::*;
import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

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
  logic       busy;
  logic       done;
  logic       broadcast;
  length_t    payload_length;
  ipv4_hdr_t  ipv4_hdr;
  mac_hdr_t   mac_hdr;

  modport in_tx  (input  dat, val, sof, eof, err, ipv4_hdr, mac_hdr, payload_length, broadcast, rdy, output req, busy, done); // used for transmitting ipv4 
  modport out_tx (output dat, val, sof, eof, err, ipv4_hdr, mac_hdr, payload_length, broadcast, rdy, input  req, busy, done); // used for transmitting ipv4 

  modport in_rx  (input  dat, val, sof, eof, err, ipv4_hdr, mac_hdr, payload_length); // used for receiving ipv4 
  modport out_rx (output dat, val, sof, eof, err, ipv4_hdr, mac_hdr, payload_length); // used for receiving ipv4 
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
  parameter bit                        DHCP_VERBOSE         = 1
)                       
(
  input logic              clk,
  input logic              rst,
  mac.in                   rx,
  mac.out                  tx,
  input dev_t              dev,
  // Connects to ARP table
  output ipv4_t                  ipv4_req, // Requested IPv4 to ARP table
  input  mac_addr_t              mac_rsp,  // MAC address response from ARP table for ipv4_req
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
  
  logic [N_TCP+1:0] act_ms;
  logic rdy, req;
  
  logic [N_TCP-1:0][7:0] tcp_ipv4_tx_d;
  logic [N_TCP-1:0]      tcp_ipv4_tx_v;
  
  logic      [N_TCP+1:0][7:0] tx_dat_vect;
  logic      [N_TCP+1:0]      tx_val_vect;      
  logic      [N_TCP+1:0]      tx_sof_vect;      
  logic      [N_TCP+1:0]      tx_eof_vect;      
  logic      [N_TCP+1:0]      tx_rdy_vect;      
  ipv4_hdr_t [N_TCP+1:0]      tx_ipv4_hdr_vect; 
  mac_hdr_t  [N_TCP+1:0]      tx_mac_hdr_vect;  
  logic      [N_TCP+1:0]      tx_broadcast_vect;
  logic      [N_TCP+1:0]      tx_req_vect;      
  logic      [N_TCP+1:0]      tx_busy_vect;     
  logic      [N_TCP+1:0]      tx_done_vect;     

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
  
    .req      (req),
    .rdy      (rdy),
  
    .ipv4_req (ipv4_req),
    .mac_rsp  (mac_rsp),
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
  
  genvar i;
  
  generate
    for (i = 0; i < N_TCP; i = i + 1) begin : gen_if
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
        .WAIT_TICKS       (TCP_WAIT_TICKS[i])
      ) tcp_vlg_inst (
        .clk       (clk),
        .rst       (rst),
        .dev       (dev),
        .port      (port[i]),
        .rx        (gen_if[i].tcp_ipv4_rx),
        .tx        (gen_if[i].tcp_ipv4_tx),
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
      assign gen_if[i].tcp_ipv4_rx.dat            = ipv4_rx.dat;
      assign gen_if[i].tcp_ipv4_rx.val            = ipv4_rx.val;
      assign gen_if[i].tcp_ipv4_rx.sof            = ipv4_rx.sof;
      assign gen_if[i].tcp_ipv4_rx.eof            = ipv4_rx.eof;
      assign gen_if[i].tcp_ipv4_rx.err            = ipv4_rx.err;
      assign gen_if[i].tcp_ipv4_rx.payload_length = ipv4_rx.payload_length;
      assign gen_if[i].tcp_ipv4_rx.ipv4_hdr       = ipv4_rx.ipv4_hdr;
      assign gen_if[i].tcp_ipv4_rx.mac_hdr        = ipv4_rx.mac_hdr;
      // tx connections
      // tcp -> ipv4
      assign tx_dat_vect[i+2]       = gen_if[i].tcp_ipv4_tx.dat;
      assign tx_val_vect[i+2]       = gen_if[i].tcp_ipv4_tx.val;
      assign tx_sof_vect[i+2]       = gen_if[i].tcp_ipv4_tx.sof;
      assign tx_eof_vect[i+2]       = gen_if[i].tcp_ipv4_tx.eof;
      assign tx_rdy_vect[i+2]       = gen_if[i].tcp_ipv4_tx.rdy;
      assign tx_ipv4_hdr_vect[i+2]  = gen_if[i].tcp_ipv4_tx.ipv4_hdr;
      assign tx_mac_hdr_vect[i+2]   = gen_if[i].tcp_ipv4_tx.mac_hdr;
      assign tx_broadcast_vect[i+2] = gen_if[i].tcp_ipv4_tx.broadcast;
      // ipv4 -> tcp
      assign gen_if[i].tcp_ipv4_tx.req  = tx_req_vect[i+2];
      assign gen_if[i].tcp_ipv4_tx.done = tx_busy_vect[i+2];
      assign gen_if[i].tcp_ipv4_tx.busy = tx_done_vect[i+2];
    end
  endgenerate
  
  generate
    for (i = 0; i < N_TCP + 2; i = i + 1) begin : gen_index
      assign ind = (act_ms[i] == 1'b1) ? i : 0;
    end
  endgenerate
  // icmp -> ipv4
  assign tx_dat_vect[0]       = icmp_ipv4_tx.dat;
  assign tx_val_vect[0]       = icmp_ipv4_tx.val;
  assign tx_sof_vect[0]       = icmp_ipv4_tx.sof;
  assign tx_eof_vect[0]       = icmp_ipv4_tx.eof;
  assign tx_rdy_vect[0]       = icmp_ipv4_tx.rdy;
  assign tx_ipv4_hdr_vect[0]  = icmp_ipv4_tx.ipv4_hdr;
  assign tx_mac_hdr_vect[0]   = icmp_ipv4_tx.mac_hdr;
  assign tx_broadcast_vect[0] = icmp_ipv4_tx.broadcast;
  // ipv4 -> icmp
  assign icmp_ipv4_tx.req     = tx_req_vect[0];
  assign icmp_ipv4_tx.busy    = tx_busy_vect[0];
  assign icmp_ipv4_tx.done    = tx_done_vect[0];

  // udp -> ipv4
  assign tx_dat_vect[1]       = udp_ipv4_tx.dat;
  assign tx_val_vect[1]       = udp_ipv4_tx.val;
  assign tx_sof_vect[1]       = udp_ipv4_tx.sof;
  assign tx_eof_vect[1]       = udp_ipv4_tx.eof;
  assign tx_rdy_vect[1]       = udp_ipv4_tx.rdy;
  assign tx_ipv4_hdr_vect[1]  = udp_ipv4_tx.ipv4_hdr;
  assign tx_mac_hdr_vect[1]   = udp_ipv4_tx.mac_hdr;
  assign tx_broadcast_vect[1] = udp_ipv4_tx.broadcast;
  // ipv4 -> udp
  assign udp_ipv4_tx.req      = tx_req_vect[1];
  assign udp_ipv4_tx.busy     = tx_busy_vect[1];
  assign udp_ipv4_tx.done     = tx_done_vect[1];

  // Common interfaces to IPv4 TX multiplexer (ipv4_vlg_tx_mux)
  ipv4_vlg_tx_mux #(N_TCP + 2) ipv4_vlg_tx_mux_isnt (
    .clk (clk),
    .rst (rst),
    // Interface UDP, TCP and ICMP
    .dat_vect       (tx_dat_vect),       // Data vector
    .val_vect       (tx_val_vect),       // Data valid available vector
    .sof_vect       (tx_sof_vect),       // Data start-of-frame vector
    .eof_vect       (tx_eof_vect),       // Data end-of-frame vector
    .rdy_vect       (tx_rdy_vect),       // Data to IPv4 ready vector
    .req_vect       (tx_req_vect),       // Data request to IPv4 vector
    .busy_vect      (tx_busy_vect),      // Data request to IPv4 vector
    .done_vect      (tx_done_vect),      // Data request to IPv4 vector
    .ipv4_hdr_vect  (tx_ipv4_hdr_vect),  //
    .mac_hdr_vect   (tx_mac_hdr_vect),   //
    .broadcast_vect (tx_broadcast_vect), //
    // Interface IPv4
    .ipv4           (ipv4_tx)
  );

endmodule

module ipv4_vlg #(
  parameter bit VERBOSE = 1
)
(
  input logic clk,
  input logic rst,

  mac.in  mac_rx,
  mac.out mac_tx,
  input  dev_t dev,

  input  logic rdy,
  output logic req,
// ARP request/response
  output ipv4_t    ipv4_req,
  input mac_addr_t mac_rsp,
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
    .rx   (mac_rx),
    .ipv4 (ipv4_rx),
    .dev  (dev)
  );
  
  ipv4_vlg_tx #(
    .VERBOSE (VERBOSE)
  ) ipv4_vlg_tx_inst (
    .clk      (clk),
    .rst      (rst),
    .tx       (mac_tx),
    .ipv4     (ipv4_tx),
    .dev      (dev),
    .rdy      (rdy),
    .req      (req),
    .ipv4_req (ipv4_req),
    .mac_rsp  (mac_rsp),
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
  mac.in      rx,
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
      ipv4.ipv4_hdr <= 0;
    end
    else begin
      hdr[IPV4_HDR_LEN-1:1] <= hdr[IPV4_HDR_LEN-2:0];
      if (byte_cnt == IPV4_HDR_LEN-2) begin
        ipv4.ipv4_hdr[159:0] <= hdr[19:0];
        ipv4.payload_length <= hdr[17:16] - 20;
      end
      if (rx.sof && (rx.hdr.ethertype == eth_vlg_pkg::IPv4)) begin
        ihl_bytes <= {rx.dat[3:0], 2'b00}; 
        receiving <= 1;
      end
      if (receiving && (byte_cnt == (ihl_bytes - 1))) hdr_done <= 1;
      if (rx.val) begin
        if (byte_cnt[0]) chsum <= chsum + {chsum_hi, rx.dat};
        if (!byte_cnt[0]) chsum_hi <= rx.dat;
        if (receiving) byte_cnt <= byte_cnt + 1;
      end
      ipv4.dat <= rx.dat;
      ipv4.sof <= receiving && (byte_cnt == IPV4_HDR_LEN - 1);
      ipv4.eof <= hdr_done && (byte_cnt == ipv4.ipv4_hdr.length - 2);
      if (ipv4.eof) begin
        if (VERBOSE) $display("%d.%d.%d.%d: IPv4 RX from %d.%d.%d.%d",
          dev.ipv4_addr[3],
          dev.ipv4_addr[2],
          dev.ipv4_addr[1],
          dev.ipv4_addr[0],
          ipv4.ipv4_hdr.src_ip[3],
          ipv4.ipv4_hdr.src_ip[2],
          ipv4.ipv4_hdr.src_ip[1],
          ipv4.ipv4_hdr.src_ip[0]
        );
      end
    end
  end
  
  assign ipv4.val   = (hdr_done && (ipv4.ipv4_hdr.dst_ip == dev.ipv4_addr || ipv4.ipv4_hdr.dst_ip == IPV4_BROADCAST));
  assign ipv4.err = rx.err;
  assign fsm_rst  = (ipv4.eof || ipv4.err);
  assign hdr[0] = rx.dat;
  
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
  mac.out       tx,
  ipv4.in_tx    ipv4,
  input  dev_t  dev,
  input  logic  rdy,
  output logic  req,
  // ARP table request/response
  output ipv4_t    ipv4_req,
  input mac_addr_t mac_rsp,
  input logic      arp_val,
  input logic      arp_err
);

  logic fsm_rst;
  logic hdr_done;
  
  logic [IPV4_HDR_LEN-1:0][7:0] hdr;
  logic [IPV4_HDR_LEN-1:0][7:0] hdr_calc;
  logic [15:0] byte_cnt;
  
  
  logic [15:0] chsum;
  logic [18:0] chsum_carry;
  logic [3:0] calc_byte_cnt;
  logic calc;
  logic calc_done;
  logic [7:0] hdr_tx;
  
  assign tx.hdr.src_mac_addr = dev.mac_addr;
  
  always @ (posedge clk) begin
    if (fsm_rst) begin
      calc          <= 0;
      hdr_calc      <= 0;
      chsum_carry   <= 0;
      calc_byte_cnt <= 0;
      hdr_done      <= 0;
      calc_done     <= 0;
      byte_cnt      <= 0;
      ipv4.req      <= 0;
      tx.val        <= 0;
      ipv4_req      <= 0;
      ipv4.busy     <= 0;
      hdr           <= 0;
    end
    else begin
      if (ipv4.rdy && !ipv4.busy) begin // If data is available, latch the header for that data. !ipv4.busy to latch only once
        ipv4.busy         <= 1;
        hdr_calc[19]      <= {ipv4.ipv4_hdr.ver, ipv4.ipv4_hdr.ihl};
        hdr_calc[18]      <= ipv4.ipv4_hdr.qos;
        hdr_calc[17:16]   <= ipv4.ipv4_hdr.length;
        hdr_calc[15:14]   <= ipv4.ipv4_hdr.id;
        hdr_calc[13][7]   <= 0;
        hdr_calc[13][6]   <= ipv4.ipv4_hdr.df;
        hdr_calc[13][5]   <= ipv4.ipv4_hdr.mf;
        hdr_calc[13][4]   <= 0;
        hdr_calc[13][3:0] <= ipv4.ipv4_hdr.fo[11:8];
        hdr_calc[12]      <= ipv4.ipv4_hdr.fo[7:0];
        hdr_calc[11]      <= ipv4.ipv4_hdr.ttl;
        hdr_calc[10]      <= ipv4.ipv4_hdr.proto;
        hdr_calc[9:8]     <= 0;
        hdr_calc[7:4]     <= ipv4.ipv4_hdr.src_ip;
        hdr_calc[3:0]     <= ipv4.ipv4_hdr.dst_ip;
        calc <= 1; // Calculate chsum first
      end
      else if (calc) begin
        ipv4_req      <= ipv4.ipv4_hdr.dst_ip; // Request MAC for destination IP
        calc_byte_cnt <= calc_byte_cnt + 1;
        chsum_carry   <= chsum_carry + hdr_calc[1:0]; // Shift latched header and add up to chsum and carry
        hdr_calc[IPV4_HDR_LEN-3:0] <= hdr_calc[IPV4_HDR_LEN-1:2];
        if (calc_byte_cnt == (IPV4_HDR_LEN/2)) begin // Done with chsum
          calc_done    <= 1; // Ready to readout data
          calc         <= 0;
          hdr[19]      <= {ipv4.ipv4_hdr.ver, ipv4.ipv4_hdr.ihl};
          hdr[18]      <= ipv4.ipv4_hdr.qos;
          hdr[17:16]   <= ipv4.ipv4_hdr.length;
          hdr[15:14]   <= ipv4.ipv4_hdr.id;
          hdr[13][7]   <= 0;
          hdr[13][6]   <= ipv4.ipv4_hdr.df;
          hdr[13][5]   <= ipv4.ipv4_hdr.mf;
          hdr[13][4]   <= 0;
          hdr[13][3:0] <= ipv4.ipv4_hdr.fo[11:8];
          hdr[12]      <= ipv4.ipv4_hdr.fo[7:0];
          hdr[11]      <= ipv4.ipv4_hdr.ttl;
          hdr[10]      <= ipv4.ipv4_hdr.proto;
          hdr[9:8]     <= chsum;
          hdr[7:4]     <= ipv4.ipv4_hdr.src_ip;
          hdr[3:0]     <= ipv4.ipv4_hdr.dst_ip;
        end
      end
      if (calc_done && (arp_val || ipv4.broadcast)) begin // done calculating chsum, header complete now. ready to transmit when MAC from ARP table is valid
        tx.hdr.ethertype    <= eth_vlg_pkg::IPv4;
        tx.hdr.dst_mac_addr <= ipv4.broadcast ? '1 : mac_rsp; // acquire destination MAC from ARP table or assign it broadcast
        //tx.hdr.length       <= ipv4.ipv4_hdr.length + (ipv4.ipv4_hdr.ihl << 2);
        hdr[IPV4_HDR_LEN-1:1] <= hdr[IPV4_HDR_LEN-2:0];
        byte_cnt <= byte_cnt + 1;
        tx.sof   <= (byte_cnt == 0);
        tx.val   <= 1;
        if (byte_cnt == IPV4_HDR_LEN-3) ipv4.req <= 1;    // read out data from buffer. Tx mux needs 4 ticks to start output
        if (byte_cnt == IPV4_HDR_LEN) hdr_done <= 1; // Done transmitting header, switch to buffer output
      end
    end
  end
  
  assign chsum = ~(chsum_carry[18:16] + chsum_carry[15:0]); // Calculate actual chsum
  always @ (posedge clk) hdr_tx <= hdr[IPV4_HDR_LEN-1];
  
  assign tx.dat = (hdr_done) ? ipv4.dat : hdr_tx; // Switch data output between header and buffer's output
  assign fsm_rst = (rst || ipv4.eof || arp_err);
  assign tx.eof = ipv4.eof;
  assign ipv4.done = ipv4.eof;

endmodule : ipv4_vlg_tx

module ipv4_vlg_tx_mux #(
    parameter N = 3
  )
  (
    input logic               clk,
    input logic               rst,
    // Interface UDP, TCP and ICMP
    input  logic      [N-1:0][7:0] dat_vect,      // Data vector
    input  logic      [N-1:0]      val_vect,      // Data valid available vector
    input  logic      [N-1:0]      sof_vect,      // Data start-of-frame vector
    input  logic      [N-1:0]      eof_vect,      // Data end-of-frame vector
    input  logic      [N-1:0]      rdy_vect,      // Data to IPv4 ready vector
    input  ipv4_hdr_t [N-1:0]      ipv4_hdr_vect, // IPv4 header vector
    input  mac_hdr_t  [N-1:0]      mac_hdr_vect,  // MAC header vector
    input  logic      [N-1:0]      broadcast_vect,// Brodcast flag vector
    output logic      [N-1:0]      req_vect,      // Data request to IPv4 vector
    output logic      [N-1:0]      busy_vect,     // Data request to IPv4 vector
    output logic      [N-1:0]      done_vect,     // Data request to IPv4 vector
    // Interface IPv4
    ipv4.out_tx                    ipv4
  );
  
  wor [$clog2(N+1)-1:0] ind;
  logic [N-1:0] rdy_msb;

  onehot #(N, 1'b1) onehot_msb_inst (
    .i (rdy_vect),
    .o (rdy_msb)
  );
  
  always @ (posedge clk) begin
    if (rst) begin
      ipv4.dat <= 0;      
      ipv4.val <= 0;      
      ipv4.sof <= 0;      
      ipv4.eof <= 0;      
      ipv4.rdy <= 0;      
      ipv4.ipv4_hdr <= 0; 
      ipv4.mac_hdr <= 0;  
      ipv4.broadcast <= 0;
    end
    else begin     
      ipv4.dat       <= dat_vect[ind];
      ipv4.val       <= val_vect[ind];
      ipv4.sof       <= sof_vect[ind];
      ipv4.eof       <= eof_vect[ind];
      ipv4.rdy       <= rdy_msb[ind];
      ipv4.ipv4_hdr  <= ipv4_hdr_vect[ind];
      ipv4.mac_hdr   <= mac_hdr_vect[ind];
      ipv4.broadcast <= broadcast_vect[ind];
    end
  end
  
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen
      assign ind = (rdy_msb[i] == 1) ? i : 0;
      always @ (posedge clk) begin
        if (rst) begin
          req_vect[i]  <= 0;
          busy_vect[i] <= 0;
          done_vect[i] <= 0;
        end
        else begin
          req_vect[i]  <= rdy_msb[i] & ipv4.req;
          busy_vect[i] <= rdy_msb[i] & ipv4.busy;
          done_vect[i] <= rdy_msb[i] & ipv4.done;
        end
      end
    end
  endgenerate
  

endmodule : ipv4_vlg_tx_mux
