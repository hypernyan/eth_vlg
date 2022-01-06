interface udp_ctl_ifc; // provide control over udp connection
  import eth_vlg_pkg::*;
  import ipv4_vlg_pkg::*;
  port_t      loc_port; // local port

  ipv4_t      ipv4_rx;     // current datagram source ip
  port_t      rem_port_rx; // target remote port
  
  length_t    length;      // current frame length
  ipv4_t      ipv4_tx;     // target ip for transmission
  port_t      rem_port_tx; // target remote port

  modport in  (input  ipv4_tx, rem_port_tx, loc_port, length, output ipv4_rx, rem_port_rx);
  modport out (output ipv4_tx, rem_port_tx, loc_port, length, input  ipv4_rx, rem_port_rx);
  modport sva (input  ipv4_tx, rem_port_tx, loc_port, length,        ipv4_rx, rem_port_rx);
endinterface : udp_ctl_ifc