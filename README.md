 # eth_vlg
Modular Ethernet HDL project.

## Description
This project's goal is to create a silicon independent, compact, modular, yet easy to implement HDL for Ethenet communications. It is written in SystemVerilog with extensive use of interfaces, structs and other synthesyzable constructs. The code is completely off any licenses and may be used by anyone for any purpose.

## Features
- Functional TCP/IP stack capable of listening and connecting;
- ARP and ICMP;
- Configurable number of TCP clients/servers;
- Generic SystemVerilog;
- 1-Gbit GMII MAC.
### Limitations
- No SACK;
- No compliance to RFC;
- Limited simulation and hardware tests;
- Not tested with Xilinx though compiled successfully (Vivado 2019.1).
### Known issues
- Problems with GMII timing constraints on lower speed devices (Cyclone V, Cyclone 10 LP)
- If TCP_TX_QUEUE_DEPTH is set higher than 14 bits, tx_queue will read 8'h00 regardless of data stored. This is probably due to timing. Observed on both Cyclone V and Cyclone 10 LP. This problem somewhat limits throughput due to low buffer size.
# How to use
To use this core, you'll need a 10/100/1000 Mbit GMII/RGMII capable PHY. One popular example is Realtek RTL8211 which doesn't even need any MDIO configuration to work. The top-level entity is `eth_vlg` described in `eth_vlg.sv` It is clocked by a single 125MHz clock `phy_rx_clk`. The `phy_tx_clk` is a loopback from it. User interface is also clocked by `phy_rx_clk`.

## Configuring the core
The top-level parameters provide flexibility in configuring the core.

`Table 1:`
| Parameter           |      Description                                   | Default |
|:--------------------|:---------------------------------------------------|:--------|
|MAC_ADDR             |48-bit local MAC                                    |0        |
|IPV4_ADDR            |32-bit local IPv4                                   |0        |
|N_TCP                |Number of TCP cores                                 |1        |
|MTU                  |Maximum Transmission Unit                           |1400     |
|TCP_RETRANSMIT_TICKS |Interval between retransmissions                    |1000000  |
|TCP_RETRANSMIT_TRIES |Tries to retransmit  before abort                   |5        |
|TCP_RAM_DEPTH        |Address width of 8-bit TX buffer RAM                |12       |        
|TCP_PACKET_DEPTH     |Address width of TX RAM for packets information     |8        |   
|TCP_WAIT_TICKS       |Assemble a packet and send it if no new bytes       |100      | 

## Interfacing the core
The top-level ports provide real-time connection control and monitoring.

`Table 2:`
| Port               | in/out      |Width   | Description                                             |
|:-------------------|:------------|:-------|:--------------------------------------------------------|
| phy.in  phy_rx     |in           |1       |Receive part of GMII interface                           |
| phy.out phy_tx     |out          |1       |Transmit part of GMII interface                          |
| clk                |in           |1       |125 MHz clock (same as phy_rx.clk)                       |
| rst                |in           |1       |Acive-high reset synchronous to clk                      |
| udp_tx             |in           |        |Not used                                                 |
| udp_rx             |out          |        |Not used                                                 |
| tcp_din, tcp_vin   |in           |N_TCP   |Outcoming TCP stream. User interface                     |
| tcp_cts            |out          |N_TCP   |Clear-to-send. Must deassert vin 1 tick after it goes '1'|
| tcp_dout, tcp_vout |out          |N_TCP   |Incoming TCP stream. User interface                      |
| rem_ipv4           |in           |N_TCP   |target 32-bit IPv4 address                               |
| loc_port           |in           |N_TCP   |local port to listen to or establish connecion           |
| rem_port           |in           |N_TCP   |remote port to establish connection to                   |
| connect            |in           |N_TCP   |connection trigger. assert to try to connect             |
| connected          |out          |N_TCP   |becomes '1' when connection is established               |
| listen             |in           |N_TCP   |transfer the core into listen mode                       |

# Architecture
The logic of the stack is seperated based on the protocol each module handles. Here, handling a protocol means to parse and remove it's header when receiving and attach a new generated header when transmitting. For example, IPv4 handler is responsible to parse the IPv4 header. Each handler module then (if packet received successfully) outputs valid signal and information about the packet to other modules.
The protol handler are:
- MAC (mac\_vlg.sv)
- ARP (arp\_vlg.sv)
- IPv4 (ipv4\_vlg.sv, ipv4\_top\_vlg.sv)
- ICMP (icmp\_vlg.sv)
- TCP (tcp\_vlg.sv)

For Transmit path, there are sometimes several handlers interfacing a signle one, for example IPv4 interfaces with ICMP, UDP and TCP. For this, a generic arbiter is used. The arbiter indepenently receives packets from several sources and processes them to a single handler in order.

```        
Receive path:          
        +=====>ARP Rx<--->ARP_ABLE
MAC====>|                   +====> ICMP Rx
        +==== =>IPv4 Rx====>|====> UDP Rx
                            +====> TCP Rx ---> TCP_CORE ---> USER LOGIC

Transmit path:          
        |A|<===ARP Tx<--->ARP_ABLE
MAC<====|R|                  |       |A|<=== ICMP Tx
        |B|<==============IPv4 Tx<===|R|<=== UDP Tx
                                     |B|<=== TCP Tx <--- TCP_TX_QUEUE <--- USER LOGIC

<===> handler-to-handler
<---> specific logic
ARB - arbiter (bug_mng)
```
## MAC
MAC interfaces PHY outside the FPGA with a GMII interface and with subsequent logic with `mac` interface defined in mac_vlg and MAC header information. FCS is handled by MAC too.
### Receive
When receiving a packet, MAC checks for correct preamble and delimiter. After that, if the packet's destination MAC is equal to local MAC set by the MAC_ADDR parameter or if it's broadcast (xFF:...), `mac_vlg_rx` fills the MAC header fields: destination and source MAC addresses and Ethertype and passes the stripped packet and header information to ARP and IPv4.
MAC handler continiously recalculates the 32-bit Frame Check Sequence and compares it with the last four bytes received. If equal, MAC generates EOF indicating that packet reception is complete. MAC also passes information extracted from Etherent header of the received packet in a mac_hdr structure. Based on Ethertype, for instance, subesquent handlers are triggered.
### Transmit
The transmit part interfaces ARP and IPv4 through `buf_mng` arbiter. After writing a packet to `buf_mng`, it will trigger `mac_vlg_tx` to start creating a packet of ARP or IPv4 Ethertype.
Ethernetheader as well as Preamble, SFD and FCS are appended to a frame and passed to PHY via phy interface. 
## IPv4

ipv4\_vlg\_top module contains ipv4 related logic including ICPM, UDP and TCP. ipv4\_vlg\_top directly interfaces user logic with raw TCP streams and TCP control/status ports.
ipv4\_top transmission logic is based on buf_mng arbiter module which asynchronously
receives packets from ICMP, UDP and TCP and queues them for transmission to MAC.

### tcp_vlg

`tcp_vlg` contains all logic responsible for TCP operation. It consists of several modules:
- `tcp_vlg_rx` Receiver handler. Parses incoming packets
- `tcp_vlg_tx` Transmit handler. Composes packets to transmit
- `tcp_vlg_tx_queue` is responsible for retransmission logic and payload checksum calculation. It stores raw TCP data from user logic in 8-bit RAM. Information such as length, sequence number and checksum is stored for each packet in a seperate `pkt_info` RAM. Information stored also includes retransmission-specific information. When a new packet is pending for transmission, space in allocated in transmission queue data RAM and a corrseponding entry is created in info RAM with all necssary information. The latter RAM is constantly scanned through and logic keeps track of unacked packets and tries to retransmit them after time based on TCP_RETRANSMIT_TICKS. `tcp_vlg_tx_queue` also generates a cts signal. The cts logic allows user to stop data stream 1 tick after ctr goes low to avoid data loss (or wiring cts signal to user logic instead of using a trigger).
- `tcp_vlg_server` TCP core. The state machine here handles connection establishment, and termination. The user control interface is implemented here described in Table 2.  Depending on run-time signals `connect` and `listen`, server can connect by IPv4 or listen for incoming connection.
### Server logic

After reset, the FSM is in idle state. Asserting `listen` signal will transition to a state which listens to incoming connection, that is, a packet with SYN flag set targeting local TCP port. Asserting `connect` signal will generate a TCP packet targeting `rem_port` TCP port and `rem_ipv4` IPv4 address. After either signal is asserted, a structure called *Transmission Control Block* or *TCB* is filled with information about connection being created.
After successfully performing the three-way handshake, the FSM results is in *connected* state in which data transfer takes place.
TCB rem_ack and rem_seq are being updated with TCP packets received and loc_ack and loc_seq are being updated from internal logic.
### Transmission queue and retransmissions

TCP receiver does not need to acknowledge each packet, instead it may cknowledge multiple packets if all were received successfully. This implies that sender stores all unacknowledged data and may retransmit unacknowledged packets.
Transmission queue stores user data in RAM which is filled with new data and freed as remote acknowledge progresses. It also stores information about each packet written: sequence number, length and checksum in a separate RAM `pkt_info` in A packet is considered complete and is queued if:
- MSS is reached
- `tcp_vin` was held low for at least TCP_TX_TIMEOUT ticks (default: 50).

and a new entry in `pkt_info` is created.
Queue's FSM continiously scans packet info RAM for entries with present flag set. Present flag indicates that a packet is stored in data RAM. Depending on packet's sequence number and remote acknowledgment number, one of the events will occur:
- Packet's *sequence* number plus packet's *length* is **less or equal** than remote *acknowledgment* number indicates that packet is acked. Present flag will be cleared releasing entry for next packets
- Packet's *sequence* number plus packet's length is **higher** than remote *acknowledgment* number and retransmit timer is less than timeout value. This situation indicates that packet is yet unacknowledged, but there is still time for remote device to acknowledge it. Retransmit timer is incremented.
- Packet's *sequence* number plus packet's *length* is **higher** than remote *acknowledgment* number and *retransmit timer* is **equal** to *timeout* value indicates that packet is unacknowledged and retransmission timeout is reached. Retransmission occurs, number of retransmission tries is incremented and retransmit timer is reset to zero. Note that when a new entry is created, retransmit timer is preloaded with timeout value, so the first time a new packet is transmitted without waiting for retransmission timeout.
- Retransmit tries reaching limit will trigger forced connection termination.

IPv4 checksum is recalculated with each new byte written.

Transmission queue is directly wired to user transmission logic with inputs `tcp_din`, `tcp_vin`
and an output `tcp_cts`.

Each protocol a used in eth_vlg has
## ARP
ARP is responsible for binding IPv4 address with MAC. Because of ARP, one must not know remote MAC address, but only IPv4.
`arp_vlg` replies to ARP requests and generates ARP requests if MAC is not known for target's IPv4 address.
## Simulation
Simple testbench is provided to verify functionality. Run modelsim.bat. (modelsim.exe location should be in PATH)
2 modules are instantiated, for client and server. After ARP, 3-way handshake is performed and data is streamed in both directions.
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
