interface dhcp_ctl_ifc;
  import ipv4_vlg_pkg::*;
  import dhcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  ipv4_t pref_ip;  // Try to aquire this IP
  logic  start;    
  ipv4_t assig_ip; 
  logic  ready;    
  logic  lease;    

  logic   router_ipv4_addr_val;
  ipv4_t  router_ipv4_addr;
  logic   subnet_mask_val;
  ipv4_t  subnet_mask;

  modport in       (input  pref_ip, start, output lease, assig_ip, ready, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
  modport out      (output pref_ip, start, input  lease, assig_ip, ready, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
  modport stat_in                         (input  lease, assig_ip, ready, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
  modport stat_out                        (output lease, assig_ip, ready, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
  modport sva      (input pref_ip, start,         lease, assig_ip, ready, router_ipv4_addr_val, router_ipv4_addr, subnet_mask_val, subnet_mask);
endinterface : dhcp_ctl_ifc