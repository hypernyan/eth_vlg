
package statistics_pkg;

  import mac_vlg_pkg::*;
  import icmp_vlg_pkg::*;
  import udp_vlg_pkg::*;
  import tcp_vlg_pkg::*;
  import ipv4_vlg_pkg::*;
  import arp_vlg_pkg::*;
  import eth_vlg_pkg::*;

  class statistics_c;
  // task automatic measure_delay;
  //   ref logic [7:0] din;
  //   ref logic       vin;
  //   ref logic [7:0] dout;
  //   ref logic       vout;
  //
  //   ref logic [7:0] tcp_din;  
  //   ref logic       tcp_vin;
  //   ref logic [7:0] tx_din;   
  //   ref logic       tx_vin;
  //   ref logic [7:0] rx_din;   
  //   ref logic       rx_vin;
  //   ref logic [7:0] tcp_dout; 
  //   ref logic       tcp_vout;
  //
  //   int ctr = 0;
  //   bit meas = 0;
  //  //while (active) begin
  //  //  #(`CLK_PERIOD)
  //  //  if (tcp_vin)  $display("Raw delay: %d", ctr*8);
  //  //  if (tx_vin)   $display("Raw delay: %d", ctr*8);
  //  //  if (rx_vin)   $display("Raw delay: %d", ctr*8);
  //  //  if (tcp_vout) $display("Raw delay: %d", ctr*8);
  //  //  if (meas) ctr = ctr + 1;
  //  //end
  //   $display("Raw delay: %d", ctr*8);
  //   $display("Total delay: %d", ctr*8 -);
  //   $display("Data to output delay: %d", ctr*8);
  // endtask : measure_delay
  endclass : statistics_c

endpackage : statistics_pkg
