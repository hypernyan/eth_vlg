
interface dhcp;
  import ipv4_vlg_pkg::*;
  import dhcp_vlg_pkg::*;

  dhcp_vlg_pkg::dhcp_hdr_t      hdr; // Packed header
  dhcp_vlg_pkg::dhcp_opt_hdr_t  opt_hdr; // Packed options header
  dhcp_vlg_pkg::dhcp_opt_pres_t opt_pres;
  dhcp_vlg_pkg::dhcp_opt_len_t  opt_len;
  logic                         val;
  logic                         done;
  logic                         err;
  ipv4_vlg_pkg::ipv4_t          src_ip;
  ipv4_vlg_pkg::ipv4_t          dst_ip;
  ipv4_vlg_pkg::id_t            ipv4_id;

  modport in  (input hdr, opt_hdr, opt_pres, opt_len, val, err, src_ip, dst_ip, ipv4_id, output done);
  modport out (output hdr, opt_hdr, opt_pres, opt_len, val, err, src_ip, dst_ip, ipv4_id, input done);
  modport sva (input hdr, opt_hdr, opt_pres, opt_len, val, err, src_ip, dst_ip, ipv4_id,        done);
endinterface : dhcp

interface dhcp_ctl;
  import ipv4_vlg_pkg::*;
  import dhcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  ipv4_t pref_ip;  // Try to aquire this IP
  logic  start;    // Initialize DHCP DORA
  ipv4_t assig_ip; // Actually assigned IP to the device
  logic  success;  // DHCP DORA was successfull. Assigned IP valid
  logic  fail;     // DHCP DORA timeout

  logic   router_ipv4_addr_val;
  ipv4_t  router_ipv4_addr;
  logic   ready;
  logic   error;
  logic   subnet_mask_val;
  ipv4_t  subnet_mask;
  modport in       (input  pref_ip, start, output success, fail, assig_ip, ready, error, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
  modport out      (output pref_ip, start, input  success, fail, assig_ip, ready, error, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
  modport stat_in                         (input  success, fail, assig_ip, ready, error, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
  modport stat_out                        (output success, fail, assig_ip, ready, error, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
  modport sva      (input pref_ip, start,         success, fail, assig_ip, ready, error, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
endinterface : dhcp_ctl