package eth_vlg_sim;

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
    
    task parse;
      input  byte            data_in [];
      output byte            data    [];
      output mac_hdr_t       mac_hdr;
      output bit             ok;
      output arp_hdr_t       arp_hdr;
      output bit             arp_ok;
      output ipv4_hdr_t      ipv4_hdr;
      output bit             ipv4_ok;
      output icmp_hdr_t      icmp_hdr;
      output bit             icmp_ok;
      output tcp_hdr_t       tcp_hdr;
      output tcp_opt_hdr_t   tcp_opt_hdr;
      output bit             tcp_ok;
      output udp_hdr_t       udp_hdr;
      output bit             udp_ok;
      output dhcp_hdr_t      dhcp_hdr;
      output dhcp_opt_hdr_t  dhcp_opt_hdr;
      output dhcp_opt_pres_t dhcp_opt_pres;
      output dhcp_opt_len_t  dhcp_opt_len;
      output bit             dhcp_ok;
  
      byte data_eth [];
      byte data_ipv4 [];
      bit fcs_ok;
      base_dev.eth_parse(data_in, data_eth, mac_hdr, fcs_ok);
      if (!fcs_ok) $error("Error: bad FCS");
      //  if (mac_hdr.dst_mac_addr != MAC_ADDRESS || mac_hdr.dst_mac_addr != '1) disable parse;
      if (!fcs_ok) disable parse;
      case (mac_hdr.ethertype)
        IPv4 : begin
          ipv4_dev.ipv4_parse(data_eth, data_ipv4, ipv4_hdr, ipv4_ok);
            $display("IPv4 detected from %d:%d:%d:%d to %d:%d:%d:%d.",
              ipv4_hdr.src_ip[3],
              ipv4_hdr.src_ip[2],
              ipv4_hdr.src_ip[1],
              ipv4_hdr.src_ip[0],
              ipv4_hdr.dst_ip[3],
              ipv4_hdr.dst_ip[2],
              ipv4_hdr.dst_ip[1],
              ipv4_hdr.dst_ip[0]
            );
          //if (ipv4_hdr.dst_ip != IPV4_ADDRESS || ipv4_hdr.dst_ip != '1) disable parse;
          case (ipv4_hdr.proto)
            ICMP : begin
            // $display("ICMP detected");
              icmp_dev.icmp_parse(data_ipv4, data, icmp_hdr, icmp_ok);
            end
            UDP : begin
            //  $display("UDP detected");
              udp_dev.udp_parse(data_ipv4, data, udp_hdr, udp_ok);
              if (udp_hdr.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT || udp_hdr.src_port == dhcp_vlg_pkg::DHCP_CLI_PORT) begin
                dhcp_dev.dhcp_parse(data, dhcp_hdr, dhcp_opt_hdr, dhcp_opt_pres, dhcp_opt_len, dhcp_ok);
              //  $display("Detected DHCP with options %p", dhcp_opt_pres);
              end
            end
            TCP : begin
            //  $display("TCP detected");
              tcp_dev.tcp_parse(data_ipv4, data, tcp_hdr, tcp_opt_hdr, tcp_ok);
            end
            default : begin
            //  $display("Unknown IPv4 protocol");
            end
          endcase
        end
        ARP : begin
        //  $display("ARP detected");
          arp_dev.arp_parse(data_eth, arp_hdr, arp_ok);
          if (arp_ok) arp_dev.arp_put(arp_hdr.src_ipv4_addr, arp_hdr.src_mac_addr);
        end
        default : begin
          $error("Task parse: Unknown Ethertype");
          disable parse;
        end
      endcase
      ok = 1;
    endtask : parse

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
        icmp_gen(src_ipv4, dst_ipv4, data_in, data_icmp, ipv4_hdr);
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
endpackage : eth_vlg_sim
