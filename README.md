 # eth_vlg
Modular Ethernet HDL project.
## Description
This project's goal is to create a silicon independent TCP/IP implementation.
## Features
- Functional TCP/IP stack capable of listening and connecting;
- DHCP client;
- ARP and ICMP;
- Configurable number of TCP clients/servers;
- Generic SystemVerilog;
- 1-Gbit RGMII MAC.
## File structure
- `src`. Source files for synthesis;
- `sim`. Source files for simulation;
- `tb`. Testbench location;
- `hw`. Hardware examples;
- `hdl_generics`. Submodule containing generic HDL components
### Limitations
- No SACK;
- No compliance to RFC;
- Limited simulation and hardware tests;
# How to use
To use this core, you'll need a 10/100/1000 Mbit GMII/RGMII capable PHY. One popular example is Realtek RTL8211 which doesn't even need any MDIO configuration to work. The top-level entity is `eth_vlg` described in `eth_vlg.sv` It is clocked by a single 125MHz clock `phy_rx_clk`. The `phy_tx_clk` is a loopback from it. User interface is also clocked by `phy_rx_clk`.
## Hello world
Sample project is provided targeting Cyclone 10 LP Evaluation Kit. The project implements ESG protocol over TCP/IP. The logic is connected to onboard LEDs D6-D9.
## Configuring the core
The top-level parametaers provide flexibility in configuring the core.

`Table 1:`
| parameter            |      Description                                                   | Default   |
|:---------------------|:-------------------------------------------------------------------|:----------|
|MAC_ADDR              |48-bit local MAC address                                            |           |
|DEFAULT_GATEWAY       |32-bit default gateway IPv4 address                                 |           |
|MTU                   |Maximum Transmission Unit                                           |1400 bytes |
|TCP_RETRANSMIT_TICKS  |Interval between retransmissions                                    |10 ms      |
|TCP_RETRANSMIT_TRIES  |Tries to retransmit a packet before aborting connection             |5 tries    |
|TCP_RAM_DEPTH         |Address width of 8-bit TX buffer RAM                                |15kB       |
|TCP_PACKET_DEPTH      |Address width of RAM which holds info for unacked TX packets        |64 packets |
|TCP_WAIT_TICKS        |Assemble a packet and send it if no new bytes                       |1 us       |
|TCP_CONNECTION_TIMEOUT|If not established/disconnected in time, abort connection           |1 s        |
|TCP_ACK_TIMEOUT       |If no new data is received in time, for pure Ack                    |125000     |
|TCP_KEEPALIVE_PERIOD  |Keepalive polling period                                            |5 s        |
|TCP_KEEPALIVE_INTERVAL|Keepalve retry period                                               |100 ms     |
|TCP_ENABLE_KEEPALIVE  |Enables keepalives                                                  |true       |
|TCP_KEEPALIVE_TRIES   |Number of keepalive retries before disconnecting                    |5 tries    |
|DOMAIN_NAME_LEN       |Length of domain name string (DHCP related)                         |           |
|HOSTNAME_LEN          |Length of host name string (DHCP related)                           |           |
|FQDN_LEN              |Length of fully qualified domain name string (DHCP related)         |           |
|DOMAIN_NAME           |Domain name string                                                  |           |
|HOSTNAME              |Host name string                                                    |           |
|FQDN                  |Fully qualified domain name string                                  |           |
|DHCP_TIMEOUT          |clock ticks before DHCP times out                                   |1 s        |
|DHCP_ENABLE           |synthesize DHCP (not used, always synthesize)                       |           |
|ARP_TABLE_SIZE        |Size of ARP table RAM                                               |256 entries|
|MAC_CDC_FIFO_DEPTH    |FIFO width for clock domain crossing between rx clock and internal  |256 bytes  |
|MAC_CDC_DELAY         |Delay before reading data from CDC FIFO after empty goes low        |3 ticks    |


## Interfacing the core
The top-level ports provide real-time connection control and monitoring.

`Table 2:`
| Port               | Direction | Description                                                        |
|:-------------------|:----------|:-------------------------------------------------------------------|
| clk                |in         |125 MHz clock (same as phy_rx.clk)                                  |
| rst                |in         |Acive-high reset synchronous to clk                                 |
| phy_rx             |in         |Receive part of GMII interface                                      |
| phy_tx             |out        |Transmit part of GMII interface                                     |
| tcp_din            |in         |Outcoming TCP data                                                  |
| tcp_vin            |in         |Outcoming TCP data valid                                            |
| tcp_cts            |out        |Clear-to-send. Deassert vin 1 tick after cts goes low               |
| tcp_snd            |out        |Force forming a packet and sending it not waiting for TCP_WAIT_TICKS|
| tcp_dout           |out        |Incoming TCP data                                                   |
| tcp_vout           |out        |Incoming TCP data valid                                             |
| rem_ipv4           |in         |Target 32-bit IPv4 address for active connection                    |
| rem_port           |in         |Remote port for active connection                                   |
| connect            |in         |Start three-way handshake (active connection)                       |
| loc_port           |in         |Local (listen) port for active or passive connection                |
| listen             |in         |Start listening                                                     |
| idle               |out        |Indicates TCP is idle                                               |
| listening          |out        |Indicates TCP is listening                                          |
| connecting         |out        |Indicates TCP is performing connection                              |
| connected          |out        |Indicates TCP connection is established                             |
| disconnecting      |out        |Indicates TCP is disconnecting                                      |
| ready              |out        |Core ready to connect                                               |
| error              |out        |Failed to obtain IP address by DHCP                                 |
| preferred_ipv4     |in         |Preffered IPv4 address to request from DHCP server                  |
| dhcp_start         |in         |Start DHCP DORA sequence to obtaion IPv4 address                    |
| assigned_ipv4      |out        |Assigned IPv4 by DHCP or preferred_ipv4 in case of DHCP failure     |
| dhcp_success       |out        |DHCP DORA was successful                                            | 
| dhcp_fail          |out        |DHCP DORA failed to complete                                        |


## Simulation
Simple testbench is provided to verify functionality. Run modelsim.bat inside `tb` folder. (modelsim.exe location should be in PATH)
2 modules are instantiated, for client and server. After DHCP sequence and ARP, 3-way handshake is performed and TCP data is streamed in both directions.
## Testing
The code was compiled with for
- Cyclone V (5CEBA5) -8 speed grade with Texas Instruments DP83867IR PHY (Quartus 17.1) on a custom PCB.
- Cyclone 10 LP -8 speed grade with RTL8211 PHY (Quartus 18.0) using QMTech Cyclone 10LP development kit.
Both failed timing, although worked as expected. Changing speed grade to -7 fixed timing.
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
