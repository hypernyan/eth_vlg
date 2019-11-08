# eth_vlg
Modular Ethernet HDL project.

## Description
This project's goal is to create a silicon independent, compact, modular, yet easy to implement HDL for Ethenet communications. It is written in SystemVerilog with extensive use of interfaces, structs and other synthesyzable constructs. 

## Features
- SystemVerilog based, generics only, no vendor-specific code (except for PLLs)
- GMII/RGMII interface MAC
- ARP with dual-port RAM-based table (reply only)
- IPv4 (options not supported)
- ICMP (Echo reply)
- UDP 
- MDIO included
### Known issues
- ICMP won't reply until ARP packed processed from ping source
- Problems with GMII timing constraints (Cyclone V)
## Simulation
Simple testbench is provided to verify functionality. Run modelsim.bat. (modelsim.exe location should be in PATH) 
## Testing
The code was compiled with Quartus 17.1 for Cyclone V -8 speed grade and tested with Texas Instruments DP83867IR PHY
## Compiling (Intel)
You can manually specify target FPGA family, part and flash memory used in create_prj.tcl. 
    set FamilyDev "Cyclone V"
    set PartDev "5CEBA5F23C8"
    set MemDev "EPCS64"
    set FlashLoadDev "5CEBA5"
The pins are modified in pins.tcl.

To compile an example project, run complete_flow.bat. (quartus.exe location should be in PATH).
To add code to your desired project, add all *.sv files that are in /src directory to your project, provide the clock, reset and phy connections.
