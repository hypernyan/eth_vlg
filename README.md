# eth_vlg
Modular Ethernet HDL project.

## Description
This project's goal is to create a silicon independent, compact, modular, yet easy to implement HDL for Ethenet communications. It is written in SystemVerilog with extensive use of interfaces, structs and other synthesyzable constructs. 

## Features
- Functional TCP/IP stack capable of listening and connecting
- Configurable number of TCP clients/servers, however timing gets worse. Tested for two.
- SystemVerilog based, generics only, no vendor-specific code.
- GMII/RGMII interface MAC.
- ARP with dual-port RAM-based table (reply only)
- IPv4 (options not supported)
- ICMP (Echo reply)
- MDIO included
### Known issues
- ICMP won't reply until ARP packed processed from ping source
- Problems with GMII timing constraints (Cyclone V)
## Simulation
Simple testbench is provided to verify functionality. Run modelsim.bat. (modelsim.exe location should be in PATH)
2 modules are instantiated, for client and server. After ARP, 3-way handshake is performed and data is streamed in both directions.
## Testing
The code was compiled with for
- Cyclone V -8 speed grade with Texas Instruments DP83867IR PHY (Quartus 17.1)
- Cyclone 10 LP -8 speed grade with RTL8211 PHY (Quartus 18.0)
