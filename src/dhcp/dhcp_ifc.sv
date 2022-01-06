
interface dhcp_ifc;
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
endinterface : dhcp_ifc