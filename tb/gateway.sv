package gateway_sim_pkg;

  import mac_vlg_pkg::*;
  import icmp_vlg_pkg::*;
  import udp_vlg_pkg::*;
  import tcp_vlg_pkg::*;
  import ip_vlg_pkg::*;
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
    device_dhcp_c dhcp_dev;
    device_ipv4_c ipv4_dev;
    device_icmp_c icmp_dev;
    device_arp_c  arp_dev;
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
    
    task proc;
      input  byte            data_in  [];
      output byte            data_out [];
      output bit             transmit;
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
      bit fcs_ok;
      bit dhcp_val_tx;
      bit val_tx;

      base_dev.eth_parse(data_in, data_eth_rx, mac_hdr_rx, fcs_ok);
      if (!fcs_ok) $error("Error: bad FCS");
      //  if (mac_hdr.dst_mac_addr != MAC_ADDRESS || mac_hdr.dst_mac_addr != '1) disable parse;
      if (!fcs_ok) disable proc;
      case (mac_hdr_rx.ethertype)
        IPv4 : begin
          ipv4_dev.ipv4_parse(data_eth_rx, data_ipv4_rx, ipv4_hdr_rx, ipv4_ok);
            $display("IPv4 detected from %d:%d:%d:%d to %d:%d:%d:%d.",
              ipv4_hdr_rx.src_ip[3],
              ipv4_hdr_rx.src_ip[2],
              ipv4_hdr_rx.src_ip[1],
              ipv4_hdr_rx.src_ip[0],
              ipv4_hdr_rx.dst_ip[3],
              ipv4_hdr_rx.dst_ip[2],
              ipv4_hdr_rx.dst_ip[1],
              ipv4_hdr_rx.dst_ip[0]
            );
          //if (ipv4_hdr_rx.dst_ip != IPV4_ADDRESS || ipv4_hdr_rx.dst_ip != '1) disable parse;
          case (ipv4_hdr_rx.proto)
            ICMP : begin
            // $display("ICMP detected");
              icmp_dev.icmp_parse(data_ipv4_rx, data_rx, icmp_hdr_rx, icmp_ok);
            end
            UDP : begin
            //  $display("UDP detected");
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
                    data_eth_tx
                  );
                  $display("packet is %p", data_eth_tx);
                end
                if (dhcp_val_tx) val_tx = 1;
                //  $display("Detected DHCP with options %p", dhcp_opt_pres);
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
          if (arp_ok) arp_dev.arp_put(arp_hdr_rx.src_ipv4_addr, arp_hdr_rx.src_mac_addr);
        end
        default : begin
          $error("Task parse: Unknown Ethertype");
          disable proc;
        end
      endcase
/*
      if (dhcp_val_tx) begin
        data_,
        data,
        mac_hdr_tx,
        val,
        arp_hdr_tx,
        arp_val_tx,
        ipv4_hdr_tx,
        ipv4_val,
        icmp_hdr,
        icmp_val,
        tcp_hdr,
        tcp_opt_hdr,
        tcp_val,
        udp_hdr,
        udp_val,
        dhcp_hdr,
        dhcp_opt_hdr,
        dhcp_opt_pres,
        dhcp_opt_len,
        dhcp_val
      );
      */
      ok = 1;
    endtask : proc

    task gen;
      input  byte           data_in [];
      output byte           data    [];
      input mac_hdr_t       mac_hdr;
      input bit             val;
      input arp_hdr_t       arp_hdr;
      input bit             arp_val;
      input ipv4_hdr_t      ipv4_hdr;
      input bit             ipv4_val;
      input icmp_hdr_t      icmp_hdr;
      input bit             icmp_val;
      input tcp_hdr_t       tcp_hdr;
      input tcp_opt_hdr_t   tcp_opt_hdr;
      input bit             tcp_val;
      input udp_hdr_t       udp_hdr;
      input bit             udp_val;
      input dhcp_hdr_t      dhcp_hdr;
      input dhcp_opt_hdr_t  dhcp_opt_hdr;
      input dhcp_opt_pres_t dhcp_opt_pres;
      input dhcp_opt_len_t  dhcp_opt_len;
      input bit             dhcp_val;
  
      byte data_eth [];
      byte data_ipv4 [];
      bit fcs_ok;
      if (icmp_val && ipv4_val && val) begin
    //    icmp_gen(src_ipv4, dst_ipv4, data_in, data_icmp, ipv4_hdr);
    //    ipv4_gen(data_icmp, data_ipv4, ipv4_hdr, src_mac, dst_mac, mac_hdr);
    //    eth_gen(data_ipv4, data, mac_hdr);
      end
      if (tcp_val && ipv4_val && val) begin
       // tcp_gen(src_ipv4, dst_ipv4, data_in, data_icmp, ipv4_hdr);
       // ipv4_gen(data_tcp, data_ipv4, ipv4_hdr, src_mac, dst_mac, mac_hdr);
       // eth_gen(data_ipv4, data, mac_hdr);        
      end
      if (dhcp_val && udp_val && ipv4_val && val) begin
        
      end
      if (arp_val && val) begin
        
      end
    endtask : gen

  endclass
endpackage : gateway_sim_pkg
