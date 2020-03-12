# eth_vlg
Modular Ethernet HDL project.

## Description
This project's goal is to create a silicon independent, compact, modular, yet easy to implement HDL for Ethenet communications. It is written in SystemVerilog with extensive use of interfaces, structs and other synthesyzable constructs. 

## Features
- Functional TCP/IP stack capable of listening and connecting
- SystemVerilog based, generics only, no vendor-specific code (except for PLLs)
- GMII/RGMII interface MAC
- ARP with dual-port RAM-based table (reply only)
- IPv4 (options not supported)
- ICMP (Echo reply)
- UDP disabled
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
## Compiling (Intel)
You can manually specify target FPGA family, part and flash memory used in create_prj.tcl.
```
    set FamilyDev "Cyclone V"
    set PartDev "5CEBA5F23C8"
    set MemDev "EPCS64"
    set FlashLoadDev "5CEBA5"
```
The pins are modified in pins.tcl.

To compile an example project, run complete_flow.bat. (quartus.exe location should be in PATH).
To add code to your desired project