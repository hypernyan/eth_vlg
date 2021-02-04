package gateway_sim_pkg;

  import mac_vlg_pkg::*;
  import icmp_vlg_pkg::*;
  import udp_vlg_pkg::*;
  import tcp_vlg_pkg::*;
  import ipv4_vlg_pkg::*;
  import arp_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import dhcp_vlg_pkg::*;

  import sim_base_pkg::*;
  import sim_ipv4_pkg::*;
  import sim_arp_pkg::*;
  import sim_udp_pkg::*;
  import sim_dhcp_pkg::*;
  import sim_icmp_pkg::*;
  import sim_tcp_pkg::*;

  typedef class device_ipv4_c;
  typedef class device_arp_c;
  typedef class device_udp_c;
  typedef class device_dhcp_c;
  typedef class device_icmp_c;
  typedef class device_tcp_c;

  class gateway_c #(
    parameter ipv4_t     IPV4_ADDRESS = 0,
    parameter mac_addr_t MAC_ADDRESS = 0

  );

    // top-level protocol handlers 
    device_base_c base_dev;
    device_dhcp_c #(
      .DEPTH               (8),
      .VERBOSE             (0),
      .IPV4_ADDRESS        ({8'd192, 8'd168, 8'd0, 8'd1}),
      .ROUTER_IPV4_ADDRESS ({8'd192, 8'd168, 8'd0, 8'd1}),
      .MAC_ADDRESS         (48'hdeadbeef01),
      .DOMAIN_NAME_LEN     (5),
      .DOMAIN_NAME         ("fpga0")
    ) dhcp_dev;
    device_ipv4_c ipv4_dev;
    device_icmp_c icmp_dev;
    device_arp_c #(
      .VERBOSE (0)
    ) arp_dev;
    device_udp_c  udp_dev;
    device_tcp_c  tcp_dev;

    function new;
      base_dev = new();
      dhcp_dev = new();
      ipv4_dev = new();
      icmp_dev = new();
      arp_dev  = new();
      udp_dev  = new();
      tcp_dev  = new();
    endfunction
    
    task automatic proc;
      input  byte     data_in  [];
      output byte     data_out [];
      output bit      transmit;
      mac_hdr_t       mac_hdr_rx;
      mac_hdr_t       mac_hdr_tx;
      bit             ok;
      arp_hdr_t       arp_hdr_rx;
      bit             arp_ok;
      ipv4_hdr_t      ipv4_hdr_rx;
      bit             ipv4_ok;
      icmp_hdr_t      icmp_hdr_rx;
      bit             icmp_ok;
      tcp_hdr_t       tcp_hdr_rx;
      tcp_opt_hdr_t   tcp_opt_hdr_rx;
      bit             tcp_ok;
      udp_hdr_t       udp_hdr_rx;
      bit             udp_ok;
      dhcp_hdr_t      dhcp_hdr_rx;
      dhcp_opt_hdr_t  dhcp_opt_hdr_rx;
      dhcp_opt_pres_t dhcp_opt_pres_rx;
      dhcp_opt_len_t  dhcp_opt_len_rx;
      bit             dhcp_ok;
      dhcp_hdr_t      dhcp_hdr_tx;
      dhcp_opt_hdr_t  dhcp_opt_hdr_tx;
      dhcp_opt_pres_t dhcp_opt_pres_tx;
      dhcp_opt_len_t  dhcp_opt_len_tx;

      byte data_eth_rx [];
      byte data_eth_tx [];
      byte data_ipv4_rx [];
      byte data_udp_rx [];
      byte data_rx [];
      bit  fcs_ok;
      bit  dhcp_val_tx;
      bit  val_tx;

      mac_hdr_rx       = 0;
      mac_hdr_tx       = 0;
      ok               = 0;
      arp_hdr_rx       = 0;
      arp_ok           = 0;
      ipv4_hdr_rx      = 0;
      ipv4_ok          = 0;
      icmp_hdr_rx      = 0;
      icmp_ok          = 0;
      tcp_hdr_rx       = 0;
      tcp_opt_hdr_rx   = 0;
      tcp_ok           = 0;
      udp_hdr_rx       = 0;
      udp_ok           = 0;
      dhcp_hdr_rx      = 0;
      dhcp_opt_hdr_rx  = 0;
      dhcp_opt_pres_rx = 0;
      dhcp_opt_len_rx  = 0;
      dhcp_ok          = 0;
      dhcp_hdr_tx      = 0;
      dhcp_opt_hdr_tx  = 0;
      dhcp_opt_pres_tx = 0;
      dhcp_opt_len_tx  = 0;
      fcs_ok           = 0;
      dhcp_val_tx      = 0;
      val_tx           = 0;
      base_dev.eth_parse(data_in, data_eth_rx, mac_hdr_rx, fcs_ok);
      if (!fcs_ok) $error("Error: bad FCS");
      if (!fcs_ok) disable proc;
      case (mac_hdr_rx.ethertype)
        IPv4 : begin
          ipv4_dev.ipv4_parse(data_eth_rx, data_ipv4_rx, ipv4_hdr_rx, ipv4_ok);
          data_eth_rx.delete();
          case (ipv4_hdr_rx.proto)
            ICMP : begin
              icmp_dev.icmp_parse(data_ipv4_rx, data_rx, icmp_hdr_rx, icmp_ok);
            end
            UDP : begin
              udp_dev.udp_parse(data_ipv4_rx, data_udp_rx, udp_hdr_rx, udp_ok);
              if (udp_hdr_rx.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT || udp_hdr_rx.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT) begin
                dhcp_dev.dhcp_parse(
                  data_udp_rx,
                  dhcp_hdr_rx,
                  dhcp_opt_hdr_rx,
                  dhcp_opt_pres_rx,
                  dhcp_opt_len_rx,
                  dhcp_ok
                );
                data_udp_rx.delete();
                if (dhcp_ok) begin   
                  dhcp_dev.pkt_handle(
                    mac_hdr_rx,
                    dhcp_hdr_rx,
                    dhcp_opt_hdr_rx,
                    dhcp_opt_pres_rx,
                    dhcp_opt_len_rx,
                    mac_hdr_tx,
                    dhcp_hdr_tx,
                    dhcp_opt_hdr_tx,
                    dhcp_opt_pres_tx,
                    dhcp_opt_len_tx,
                    dhcp_val_tx
                  );
                  dhcp_dev.dhcp_gen(
                    dhcp_hdr_tx,
                    dhcp_opt_hdr_tx,
                    dhcp_opt_pres_tx,
                    dhcp_opt_len_tx,
                    data_out
                  );
                  
                end
                if (dhcp_val_tx) transmit = 1;
              end
            end
            TCP : begin
            //  $display("TCP detected");
              tcp_dev.tcp_parse(data_ipv4_rx, data_rx, tcp_hdr_rx, tcp_opt_hdr_rx, tcp_ok);
            end
            default : begin
            //  $display("Unknown IPv4 protocol");
            end
          endcase
        end
        ARP : begin
        //  $display("ARP detected");
          arp_dev.arp_parse(data_eth_rx, arp_hdr_rx, arp_ok);
          data_eth_rx.delete();
          if (arp_ok) arp_dev.arp_put(arp_hdr_rx.src_ipv4_addr, arp_hdr_rx.src_mac);
        end
        default : begin
          $error("Task parse: Unknown Ethertype");
          disable proc;
        end
      endcase
      ok = 1;
    endtask : proc
  endclass
endpackage : gateway_sim_pkg
