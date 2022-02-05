interface tcp_ctl_ifc; // provide control over tcp connection
  import ipv4_vlg_pkg::*;

  import tcp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  logic       connect;  // try to establish a connection by IPv4
  logic       listen;   // transiton to listen state
  ipv4_t      rem_ipv4; // set target remote ip (client only)
  port_t      rem_port; // set target remote port (client only)
  port_t      loc_port; // set local port 
  port_t      con_port; // actual connected remote port 
  ipv4_t      con_ipv4; // actual connected remote ip
  tcp_stat_t  status;   // tcp engine status

  modport in  (input  connect, listen, rem_ipv4, rem_port, loc_port, output con_port, con_ipv4, status);
  modport out (output connect, listen, rem_ipv4, rem_port, loc_port, input  con_port, con_ipv4, status);
  modport sva (input  connect, listen, rem_ipv4, rem_port, loc_port,        con_port, con_ipv4, status);
endinterface : tcp_ctl_ifc
