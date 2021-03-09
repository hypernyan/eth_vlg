## Simulation environment
The simulation environment provides SystemVerilog code necessary to verify the synthesyzable `eth_vlg` functionality. Testbench is automated with the `/tb/compile.tcl` script. Currently supported simulator is Modelsim. The script compiles source and simulation files and executes the simulation. Waves are displayed according to `/tb/wave_config.do`. The top level testbench file `tb.sv` contains two instances of DUT `eth_vlg`: client and server which are synthesizable and a `gateway_sim` which is used for simulation only. Neither of logic contatined in `/sim` is synthesizable. `switch_sim` is a passive switch simulator which resends a packet to all connected devices except for the one that sent it.
```
  +---+       +--------+
  |srv|<=phy=>| switch |       +--------------+
  |DUT|       |  sim   |       | gateway sim  |
  +---+       |        |       | +---+ +----+ |
              |        |<=phy=>| |ARP| |DHCP| |
  +---+       |        |       | +---+ +----+ |
  |cli|<=phy=>|        |       +--------------+
  |DUT|       |        |   
  +---+       +--------+
```
### Object-oriented approach
The logic necessary for simulation is written using SystemVerilog classes. Packet protocol handlers are derived from the same base class which handles ethernet and low-level tasks and functions. Upper level handler classes are derived from lower level, e.g.: 
```
dhcp_vlg_sim <- udp_vlg_sim <- ipv4_vlg_sim <- base_class_sim
```
Protocol handlers `arp_vlg_sim`, `dhcp_vlg_sim`, `eth_vlg_sim`, `ipv4_vlg_sim`, `icmp_vlg_sim`, `ipv4_vlg_sim`, `tcp_vlg_sim`, `udp_vlg_sim` are responsible for parsing and generating packets of their type. ARP handler also includes ARP table functionality. DHCP server logic is described in `dhcp_srv_sim`.