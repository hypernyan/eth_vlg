# eth_vlg
Modular Ethernet HDL project.

## Description
This project's goal is to create a silicon independent, compact, modular, yet easy to implement HDL for Ethenet communications. It is written in SystemVerilog with extensive use of interfaces, structs and other synthesyzable constructs. 

## Features
- Functional TCP/IP stack capable of listening and connecting
- Configurable number of TCP clients/servers, however timing gets worse. Tested for two.
- SystemVerilog based, generics only, no vendor-specific code.
- GMII/RGMII interface MAC.
- ARP with dual-port RAM table
- IPv4 (options not supported)
- ICMP
### Limitations
- GMII interface only
- No SACK
- No compliance to RFC
- Limited simulation and hardware tests
- Not tested with Xilinx though compiled successfully (Vivado 2019.1).
### Known issues
- Problems with GMII timing constraints (Cyclone V, Cyclone 10 LP)
- If TCP_TX_QUEUE_DEPTH is set higher than 14 bits, tx_queue will read 8'h00 regardless of data stored. This is probably due to timing limitations. Observed on both Cyclone V and Cyclone 10 LP. This somewhat limits throughput because server can't use all available window.
# Architecture
The logic is composed of protocol managers:
- MAC
- ARP
- IPv4
— ICMP
— TCP
And additional logic:
- Packet multiplexers
- TCP/IP server and retransmission logic
- ARP table
## Compile-time parameters
- MTU. Maximum transmission unit. Defines maximum size in bytes of IPv4 packet
- MAC. Server MAC address
- IPv4. Server IPv4 address
- TCP_PORT. Server TCP port
- ARP_TABLE_SIZE. Depth of ARP table
- TCP_TX_QUEUE_DEPTH. Depth of TCP transmission buffer.

Other parameters:

- TCP_ACK_TIMEOUT. Time in clock ticks before Ack is transmitted without data.
- TCP_RETRANSMIT_TIMEOUT. Time in ticks before retransmissions occur
- TCP_RETRANSMIT_TRIES. Number of failed retransmissions to terminate connection

## MAC
MAC interfaces PHY outside the FPGA with a GMII interface:

input logic phy_rx_clk,
input logic [7:0] phy_rx_dat,
input logic phy_rx_val,
input logic phy_rx_err,

output logic phy_gtx_clk,
output logic [7:0] phy_tx_dat,
output logic phy_tx_val,
output logic phy_tx_err

And intrerfaces subsequent logic with mac interface defined in mac_vlg d MAC header

### RX

When receiving a packet, MAC checks for correct preamble and delimiter. After that, MAC begins filling header fields: destination and source MAC addresses and Ethertype.
MAC also calculates the 32-bit Frame Check Sequence over Ethernet header and payload, recalculates and compares the FCS at each clock cycle with last four bytes received.
If equal, MAC generates EOF indicating that packet reception is complete.
MAC also passes information about received packet in a mac_hdr structure

### TX

If MAC is not busy and mac\_hdr\_v is asserted, MAC will generate Ethernet header based on mac_hdr and begin transmission.
Transmission logic interfaces buf_mng module which holds data to be transmitted from multiple protocols simultaneously, currently ARP and IPv4.
This FIFO is asynchronously (completely independently) written by ipv4\_tx and arp\_tx.
When a compete is written to buf\_mng, it asserts 'val' signal indicating that it is holdin
g a packet. Valid mac\_hdr is also present when MAC then acknowledges this by setting rdy high.

## ipv4_vlg_top

ipv4_vlg_top module contains ipv4_vlg module which is responsible for IP 4 packet parsing and generating as well as all IPv4-based modules: ICMP, UDP and TCP. ipv4_vlg_top directly interfaces user logic with raw TCP streams and TCP control/status ports.
ipv4_top transmission logic is based on buf_mng arbiter module which asynchronously
receives packets from ICMP, UDP and TCP and queues them for transmission to MAC.

### ipv4_vlg

### tcp_vlg

`tcp_vlg` contains all logic responsible for TCP operation. It consists of several modules:
- `tcp_vlg_rx` handles packet parsing from ipv4 and passing raw TCP stream to tcp_vlg_rx_queue
- `tcp_vlg_tx` is responsible for packet generation, calculation of TCP checksum and streaming data to ipv4_vlg_top.
- `tcp_vlg_tx_queue` is responsible for retransmission logic and payload checksum calculation. It stores raw TCP data from user logic in 8-bit RAM as well as all information about packets: length, sequence number, payload checksum, ticks before next retransmission and number of retransmission tries. When a new packet is pending for transmission, queue signals server logic.
- `tcp_vlg_server` Server state machine is implemented. The state machine handles connection establishment, and termination. takes place here. Depending on run-time signals `connect` and `listen`, server can connect by IPv4 or listen for incoming connection.
### Server logic

After reset, the FSM is in idle state. Asserting `listen` signal will transition to a state which listens to incoming connection, that is, a packet with SYN flag set targeting local TCP port. Asserting `connect` signal will generate a TCP packet targeting `rem_port` TCP port and `rem_ipv4` IPv4 address. After either signal is asserted, a structure called *Transmission Control Block* or *TCB* is filled with information about connection being created.
After successfully performing the three-way handshake, the FSM results is in *connected* state in which data transfer takes place.
TCB rem_ack and rem_seq are being updated with TCP packets received and loc_ack and loc_seq are being updated from internal logic.
### Transmission queue and retransmissions

TCP receiver does not need to acknowledge each packet, instead it may cknowledge multiple packets if all were received successfully. This implies that sender stores all unacknowledged data and may retransmit unacknowledged packets.
Transmission queue stores user data in RAM which is filled with new user data and freed as remote acknowledge progresses. It also stores information about each packet written: sequence number, length and checksum in a separate RAM `pkt_info` in A packet is considered complete and is queued if:
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
