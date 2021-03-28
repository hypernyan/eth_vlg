package gateway_sim_pkg;

  import mac_vlg_pkg::*;
  import icmp_vlg_pkg::*;
  import udp_vlg_pkg::*;
  import tcp_vlg_pkg::*;
  import ipv4_vlg_pkg::*;
  import arp_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import dhcp_vlg_pkg::*;

  import base_vlg_sim::*;
  import sim_ipv4_pkg::*;
  import sim_arp_pkg::*;
  import sim_udp_pkg::*;
  import sim_dhcp_pkg::*;
  import sim_icmp_pkg::*;
  import sim_tcp_pkg::*;

  typedef class ipv4_vlg_sim;
  typedef class device_arp_c;
  typedef class device_udp_c;
  typedef class dhcp_vlg_sim;
  typedef class icmp_vlg_sim;
  typedef class device_tcp_c;

  class gateway_c #(
    parameter ipv4_t     IPV4_ADDRESS = 0,
    parameter mac_addr_t MAC_ADDRESS = 0

  );

    // top-level protocol handlers 

    dhcp_vlg_sim #(
      .DEPTH               (8),
      .VERBOSE             (1),
      .IPV4_ADDRESS        ({8'd192, 8'd168, 8'd0, 8'd1}),
      .ROUTER_IPV4_ADDRESS ({8'd192, 8'd168, 8'd0, 8'd1}),
      .MAC_ADDRESS         (48'hdeadbeef01),
      .DOMAIN_NAME_LEN     (5),
      .DOMAIN_NAME         ("fpga0")
    ) dhcp_dev;

    device_arp_c #(
      .VERBOSE (1)
    ) arp_dev;

    icmp_vlg_sim icmp_dev;

    device_tcp_c tcp_dev;

    function new;
      icmp_dev = new();
      arp_dev  = new();
      dhcp_dev = new();
      tcp_dev  = new();
    endfunction
    
    task automatic proc;
      
      input  byte     data_in  [];
      output byte     data_out [];
      output bit      transmit;

      byte data_out_icmp [];
      byte data_out_arp  []; 
      byte data_out_dhcp [];
      byte data_out_tcp  [];

      bit icmp_ok;
      bit arp_ok;
      bit dhcp_ok;
      bit tcp_ok;
      
      bit transmit_icmp;
      bit transmit_arp;
      bit transmit_dhcp;
      bit transmit_tcp;
      // Fork and process packets by available handlers in parallel
      fork
        icmp_dev.icmp_proc(data_in, data_out_icmp, icmp_ok, transmit_icmp);
        arp_dev.arp_proc  (data_in, data_out_arp,   arp_ok,  transmit_arp);
        dhcp_dev.dhcp_proc(data_in, data_out_dhcp, dhcp_ok, transmit_dhcp);
      //  tcp_dev.tcp_proc (data_in, data_out_tcp,  transmit_tcp);
      join
      if (transmit_icmp) begin
        data_out = data_out_icmp;
        transmit = 1;
      end
      if (transmit_arp) begin
        data_out = data_out_arp;
        transmit = 1;
      end
      if (transmit_dhcp) begin
        data_out = data_out_dhcp;
        transmit = 1;
      end
      // case (mac_hdr_rx.ethertype)
      //   IPv4 : begin
      //     ipv4_dev.ipv4_parse(data_eth_rx, data_ipv4_rx, ipv4_hdr_rx, ipv4_ok);
      //     data_eth_rx.delete();
      //     case (ipv4_hdr_rx.proto)
      //       ICMP : begin
      //         icmp_dev.icmp_parse(data_ipv4_rx, data_rx, icmp_hdr_rx, icmp_ok);
      //       end
      //       UDP : begin
      //         udp_dev.udp_parse(data_ipv4_rx, data_udp_rx, udp_hdr_rx, udp_ok);
      //         if (udp_hdr_rx.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT || udp_hdr_rx.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT) begin
      //           dhcp_dev.dhcp_parse(
      //             data_udp_rx,
      //             dhcp_hdr_rx,
      //             dhcp_opt_hdr_rx,
      //             dhcp_opt_pres_rx,
      //             dhcp_opt_len_rx,
      //             dhcp_ok
      //           );
      //           data_udp_rx.delete();
      //           if (dhcp_ok) begin   
      //             dhcp_dev.pkt_handle(
      //               mac_hdr_rx,
      //               dhcp_hdr_rx,
      //               dhcp_opt_hdr_rx,
      //               dhcp_opt_pres_rx,
      //               dhcp_opt_len_rx,
      //               mac_hdr_tx,
      //               dhcp_hdr_tx,
      //               dhcp_opt_hdr_tx,
      //               dhcp_opt_pres_tx,
      //               dhcp_opt_len_tx,
      //               dhcp_val_tx
      //             );
      //             dhcp_dev.dhcp_gen(
      //               dhcp_hdr_tx,
      //               dhcp_opt_hdr_tx,
      //               dhcp_opt_pres_tx,
      //               dhcp_opt_len_tx,
      //               data_out
      //             );
                  
      //           end
      //           if (dhcp_val_tx) transmit = 1;
      //         end
      //       end
      //       TCP : begin
      //       //  $display("TCP detected");
      //         tcp_dev.tcp_parse(data_ipv4_rx, data_rx, tcp_hdr_rx, tcp_opt_hdr_rx, tcp_ok);
      //       end
      //       default : begin
      //       //  $display("Unknown IPv4 protocol");
      //       end
      //     endcase
      //   end
      //   ARP : begin
      //   //  $display("ARP detected");
      //     arp_dev.arp_parse(data_eth_rx, arp_hdr_rx, arp_ok);
      //     data_eth_rx.delete();
      //     if (arp_ok) arp_dev.arp_put(arp_hdr_rx.src_ipv4_addr, arp_hdr_rx.src_mac);
      //   end
      //   default : begin
      //     $error("Task parse: Unknown Ethertype");
      //     disable proc;
      //   end
   //  endcase
   //  ok = 1;
    endtask : proc
  endclass
endpackage : gateway_sim_pkg
