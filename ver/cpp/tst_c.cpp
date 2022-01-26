// #include "../hdr/tst_c.h"

// tst_c::tst_c (
//   ipv4_c::ipv4_t    _cli_ipv4_addr  ,
//   ipv4_c::ipv4_t    _srv_ipv4_addr  ,
//   mac_c::mac_addr_t _cli_mac_addr   ,
//   mac_c::mac_addr_t _srv_mac_addr   ,
//   std::string       _cli_domain_name,
//   std::string       _srv_domain_name,
//   std::string       _cli_hostname   ,
//   std::string       _srv_hostname   ,
//   std::string       _cli_fqdn       ,
//   std::string       _srv_fqdn       ,
//   std::string       _cli_dut_string ,
//   std::string       _srv_dut_string ,
//   ipv4_c::ipv4_t    _default_gateway,
//   uint16_t          _cli_tcp_port   ,
//   uint16_t          _srv_tcp_port   ,
//   unsigned          _mtu
// ) {
    
//   cli_tb2dut = (tb2dut_t*)malloc(sizeof(tb2dut_t));
//   srv_tb2dut = (tb2dut_t*)malloc(sizeof(tb2dut_t));
//   cli_dut2tb = (dut2tb_t*)malloc(sizeof(dut2tb_t));
//   srv_dut2tb = (dut2tb_t*)malloc(sizeof(dut2tb_t));

//   cli_ipv4_addr   = _cli_ipv4_addr  ;
//   srv_ipv4_addr   = _srv_ipv4_addr  ;
//   cli_mac_addr    = _cli_mac_addr   ;  
//   srv_mac_addr    = _srv_mac_addr   ;
//   cli_domain_name = _cli_domain_name;
//   srv_domain_name = _srv_domain_name;
//   cli_hostname    = _cli_hostname   ;
//   srv_hostname    = _srv_hostname   ;
//   cli_fqdn        = _cli_fqdn       ;
//   srv_fqdn        = _srv_fqdn       ;
//   cli_dut_string  = _cli_dut_string ;
//   srv_dut_string  = _srv_dut_string ;
//   default_gateway = _default_gateway;
//   cli_tcp_port    = _cli_tcp_port   ;
//   srv_tcp_port    = _srv_tcp_port   ;
//   mtu             = _mtu            ;

//   rst = true;
//   rst_ctr = 0;
// };

// tst_c::~tst_c() {};

// uint32_t tst_c::ipv4_to_uint32 (ipv4_c::ipv4_t& ipv4) {
//   return (uint32_t)(ipv4.i[0] << 24 | (ipv4.i[1] << 16) | (ipv4.i[2] << 8) | (ipv4.i[3]));
// }

// void tst_c::tick (unsigned tim) {
//   // check that DHCP leases is active
//   switch (state) {
//     case (idle_s) : {
//       printf("=== eth_vlg testbench ===\n");
//       state = setup_s;
//       break;
//     }
//     case (setup_s) : {
//       // DHCP
//       cli_tb2dut->preferred_ipv4 = ipv4_to_uint32(cli_ipv4_addr);
//       srv_tb2dut->preferred_ipv4 = ipv4_to_uint32(srv_ipv4_addr);
//       printf("=== parameter setup ===\n");
//       // TCP
//       cli_tb2dut->tcp_rem_ipv4 = {0}; // client does not expect any specific IP
//       cli_tb2dut->tcp_rem_port = 0;   // client does not expect any specific port
//       cli_tb2dut->tcp_loc_port = cli_tcp_port;
      
//       srv_tb2dut->tcp_rem_ipv4 = {0}; // client does not expect any specific IP
//       srv_tb2dut->tcp_rem_port = cli_tcp_port; // client does not expect any specific port
//       srv_tb2dut->tcp_loc_port = srv_tcp_port;
//       state = reset_s;
//       break;
//     }
//     case (reset_s) : {
//       rst_ctr++;
//       if (rst_ctr == 10) rst = 0;
//       if (rst_ctr == 20) state = cli_dhcp_dora_s;
//       break;
//     }
//     case (cli_dhcp_dora_s) : {
//       srv_tb2dut->dhcp_start = 1;
//       state = srv_dhcp_dora_s;
//       break;
//     }
//     case (srv_dhcp_dora_s) : {
//       cli_tb2dut->dhcp_start = 0;
//       srv_tb2dut->dhcp_start = 1;
//       state = dhcp_check_s;
//       break;
//     }
//     case (dhcp_check_s) : {
//       dhcp_timeout++;
//       if (dhcp_timeout == DHCP_TIMEOUT) {
//         test_failed = 1;
//         state = done_s;
//       }
//       check_lease
//       if (
//         srv_dut2tb->dhcp_lease && srv_dev2tb->lease_valid &&
//        (srv_dut2tb->assigned_ip == srv_dev2tb->lease_valid)
      
      
//       )
//       srv_tb2dut->dhcp_start = 0;
//      // if ()
//       state = done_s;
//       break;
//     }
//     case (done_s) : {
//       break;
//     }
//   }
// }

// bool check_lease (
//   bool&           lease_user, // lease status as seen by DHCP client
//   bool&           lease_auth, // lease status as seen by DHCP server
//   ipv4_c::ipv4_t& ipv4_requested,
//   ipv4_c::ipv4_t& ipv4_leased
// ) {

// };