 # eth_vlg
```
████████╗ ████████╗ ██╗   ██╗          ██╗   ██╗ ██╗        ██████╗ 
██╔═════╝    ██╔══╝ ██║   ██║          ██║   ██║ ██║       ██╔════╝ 
████████╗    ██║    ████████║          ██║   ██║ ██║       ██║  ███╗  
██╔═════╝    ██║    ██╔═══██║          ╚██╗ ██╔╝ ██║       ██║   ██║  
████████╗    ██║    ██║   ██║ ████████╗ ╚████╔╝  ████████╗ ╚██████╔╝
╚═══════╝    ╚═╝    ╚═╝   ╚═╝ ╚═══════╝  ╚═══╝   ╚═══════╝   ╚════╝
```
Ethernet HDL project.
## Description
This project's goal is to create a silicon independent TCP/IP implementation. 
## Features
- Functional TCP/IP stack capable of listening and connecting;
- SACK-capable (tx and rx);
- ARP table and request/reply;
- ICMP reply (ping);
- DHCP client;
- 1-Gbit RGMII MAC (8-bit datapath).
## Limitations
- No compliance to RFC;
- Low tx and rx buffer sizes (only on-chip RAM used);
- Static RTO;
- Only 1 connection per instance;
- Limited simulation and hardware tests.
## Project file structure
- `src`. Source files for synthesis;
- `sim`. Source files for simulation;
- `tb`. Testbench location;
- `hw`. Hardware examples;
- `hdl_generics`. Submodule containing generic HDL components
# How to use
To use this core, a 10/100/1000 Mbit GMII/RGMII capable PHY should be connected to the FPGA. One popular example is Realtek RTL8211 which doesn't even need any MDIO configuration to work. The top-level entity is `eth_vlg` described in `eth_vlg.sv`. User data stream connections for TCP and UDP are provided via `tcp_xxx` and `udp_xxx` respectively. The control and status lines for DHCP and TCP are also there. Please note that TCP and UDP become avaliable after DHCP has either succeeded or failed to obtain an IP address.
## Clocking
The design is clocked by two (possibly asynchronous) 125MHz clocks: 
- Receive clock is provided by PHY itself as part of RGMII/GMII interface: `phy_rx_clk`. 
- Internal logic and transmit clock is provided by user via `clk` port with corresponding synchronous `rst`. Same clock as `phy_rx_clk` may be used.
### Receive path
Any clock-to-data skew is possible as the PLL in receive path allows for arbitrary phase shift (see example in `hw` folder). Receive clock provided by PHY is used only as receive PLL reference clock. All logic is including CDC is clocked by the receive PLL's output. The PLL is used to align data to clock for correct timing. This clock drives the input DDR I/O primitives used for RGMII and the write port of CDC FIFO.
### Clock domain crossing
Clock domain crossing is handled by `mac_vlg_cdc`. GMII signals from DDR input primitives are written to CDC FIFO containing true dual-port RAM in receive clock domain. These signals are then read from the FIFO to `clk` domain. The readout starts a few ticks after `empty` flag of the FIFO goes low and stops when `empty` goes high again. This delay is introduced to make sure that there is always at least one unread byte in FIFO (as seen from read side) while the packet is being simultaneously written and read. This is important as subsequent receive logic is expecting uninterrupted data validity `val` signal during reception of a single packet. While this does not pose a problem if read clock is slower then write clock or if they are coherent, interruptions in `val` may occur if read clock is faster then write clock especially with longer packets.
### Transmit path
The same clock `clk` used for clocking logic is fed to transmit clock PLL that geenrates `phy_gtx_clk` with correct phase shift in order to meet PHY's timing requirements.Reference clock for the tx PLL is supplied externally from outside the FPGA. If no 125MHz clocks are present on the PCB, one can generate two 125MHz clocks: one for internal use and the other for `phy_gtx_clk` and defined correct phase shift between these clocks.
### SDC and tuning
Sample `constaints.sdc` is supplied with Cyclone 10 LP Evaluation Kit example project: `hw/c10lp_eval_kit/src/`. Firstly, PLL clocks are defined with desired phase shifts. For Intel FPGAs it's important to note that actual synthesys parameters of PLLs are set in `rgmii_rx_pll.v` and `rgmii_rx_pll.v` located in `hw/c10lp_eval_kit/ip/`. The `altpll_component.clk0_phase_shift` sets phase shift in ns units (unlike degrees in .sdc). A warning will appear in Quartus if these parameters do not match. Receive and transmit clock domains are separated by means of `set_clock_groups -asynchronous`. The rx constraints are described using virtual clock. It may be necessary to empirically set the rx and tx PLL's phase shift to achieve stable data latching and timing requrements of PHY.
```
   ╔══════╗     ╔═══════════════════════════════════════╗
   ║      ║     ║               ╔═════╗ ╔════╗          ║
   ║   ┌──╫─dat─╫────────►╔═══╗ ║dpram║ ║sync║ ╔═══════╗║
   ║   │rx╟     ║╔═══╗    ║ddr╟─►w   r╟─►    ╟─► core  ║║
   ║   └──╫─clk─╫╢pll╟─┬─►╚═══╝ ╚▲═══▲╝ ╚═══▲╝ ║ logic ║║
   ║PHY   ╢     ║╚═══╝ └───clk───┘   └─clk──┤  ║       ║║
   ║      ╢     ║         ╔═══╗◄─────dat────┼──║       ║║
   ║   ┌──╢◄dat─╫─────────╢ddr║             │  ║       ║║
   ║   │tx║     ║╔═══╗    ╚═══╝◄┐           │  ╚═══▲═══╝║ ╔════╗
   ║   └──╢◄clk─╫╢pll╟──────────┴────clk────┴──────┴────╫─╢xtal║
   ║      ║     ║╚═══╝                                  ║ ╚════╝
   ╚══════╝     ╚═══════════════════════════════════════╝
```
## Hello world
Sample project is provided targeting Cyclone 10 LP EvaluationpKit. The project implements ESG protocol over TCP/IP. The logic is connected to onboard LEDs D6-D9.
Default IP is 192.168.1.213 if no DHCP server is on LAN. TCP port is 1000. After establishing a TCP connection with PuTTY or other tools, type:
```
`ver;
```
You should get a string response containing version and build date. 
Note: be sure to check `Raw` in connection type field if using PuTTY.
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
