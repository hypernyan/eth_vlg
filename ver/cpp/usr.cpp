#include "../hdr/usr.h"
  
  // top-level DUT interface 
usr::usr() {

}

usr::~usr() {
  printf("destructor\n");
}

  bool usr::rst(int tim) {
    return (tim < RST_HIGH_TICKS);
  }

  long usr::tb2rtls(uint64_t val, int b) {
  	long	s;
  	s = (val << (sizeof(val)*8-b));
  	s >>= (sizeof(val)*8-b);
  	return	s;
  }
  
  unsigned long usr::tb2rtlus(uint64_t val, int b) {
  	return val &= (1<<b)-1;
  }

  void usr::configure (
    uint16_t udp_loc_port,
    uint32_t udp_ipv4_tx,
    uint16_t udp_rem_port_tx,
    bool     tcp_connect,
    bool     tcp_listen,
    uint32_t tcp_rem_ipv4,
    uint32_t tcp_rem_port,
    uint16_t tcp_loc_port,
    uint32_t preferred_ipv4
  ) {
    //ifc.udp_loc_port   [idx] = udp_loc_port;
    //ifc.udp_ipv4_tx    [idx] = udp_ipv4_tx;
    //ifc.udp_rem_port_tx[idx] = udp_rem_port_tx;
    //ifc.tcp_connect    [idx] = tcp_connect;
    //ifc.tcp_listen     [idx] = tcp_listen;
    //ifc.tcp_rem_ipv4   [idx] = tcp_rem_ipv4;
    //ifc.tcp_rem_port   [idx] = tcp_rem_port;
    //ifc.tcp_loc_port   [idx] = tcp_loc_port;
    //ifc.preferred_ipv4 [idx] = preferred_ipv4;
  }

