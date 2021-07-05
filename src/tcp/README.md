
## TCP state machine
```
                              +------+        
                       +------|closed|-------+
                       |      +------+       |
                 +-----v-----+         +-----v-----+
                 |   listen  |         | send syn  |
                 +-----|-----+         +-----|-----+
                       +<-------[SYN]<-------+
                 +-----v-----+         +-----v-----+
                 |send synack|         | syn sent  |
                 +-----|-----+         +-----|-----+
                       +----->[SYN ACK]----->+    
                 +-----v-----+         +-----v-----+
                 |synack sent|         | send ack  |
                 +-----|-----+         +-----|-----+
                       +<-------[ACK]<-------+
                       |               +-----v------+
                       |               |con ack sent|
                       |               +-----|------+
                       +----------+----------+
                                  |
                              +---+---+
                              |compute| 
                              |win_scl|
                              +---|---+
                                  |
                              +---v---+
                              | init  | 
                              +---|---+   
                                  |
                          +-------v-------+    
                          |  established  |     
                          +---------------+        


```
# TCP logic architecture
The top level TCP logic is described by `tcp_vlg` which consists of three main modules:
- TCP packet parser `tcp_vlg_rx` which receives TCP frames from IPv4 and strips them off header,
- TCP packet assembler `tcp_vlg_tx` that assembles TCP frames and passes them to IPv4,
- TCP core logic `tcp_vlg_core`;
The `tcp_vlg_core` is responsible for the actual underlying TCP logic and is further divided into three main parts:
- TCP receive control `tcp_rx_ctl`,
- TCP transmit control `tcp_tx_ctl`,
- TCP engine `tcp_vlg_engine`;
More specifically, TCP receive control implements receive queue as well as Acknoweldgement Number and SAck block update logic. Transmit control
```
                   ╔══════╗               ╔══════╗            ╔══════╗ 
raw tcp from user─►║tx ctl╟─►local seq───►║engine║◄─local Ack─╢rx ctl╟─►raw tcp to user
                   ║      ╟─►tx requests─►║      ║◄─local SAck╢      ║
                   ╚══════╝               ╚══════╝            ╚══════╝
```
Interfaces are defined in `tcp_vlg_if.sv`.

```
tcp_vlg

                   ╔---tcp_core-------------------------------------------------+
                   | ╔---tcp_rx_ctl----+                                        |
+-----tcp_rx-----+ | | ╔---tcp_ack---+ |                                        |
|                |===> |             | |   ╔---tcp_engine----+  +--------+      |
+----------------+ | | +-------------+ |   |      ╔---+      |  |         \     |
                   | | +--tcp_sack---+ |   |      |FSM|========>|          \    |
      raw tcp <======= |             | |   |      +---+      |  |           \   |
                   | | +-------------+ |   | ╔tcp_keepalive+ |  |            |  | +-----tcp_tx-----+
                   | +-----------------╝   | |             |===>| tcp_tx_arb |===>|                |
                   | ╔---tcp_tx_ctl----+   | +-------------+ |  |            |  | +----------------+
                   | | ╔-tcp_tx_buf-+  |   |                 |  |           /   |
                   | | | tx dat buf |  |   | +tcp_fast_rtx-+ |  |          /    |
                   | | +------------+  |   | |             |===>|         /     |
                   | | ╔--tcp_sack--+  |   | +-------------+ |  +--------+      |
                   | | | tx pkt info|  |   +-----------------+                  |
                   | | +------------+  |                                        |
                   | +-----------------╝                                        |
                   +------------------------------------------------------------╝
```

## TCP receive control
TCP receive control is responsible for operations neccessary to properly handle packet reception and report status to the sender:
- implements receive queue for incoming data (inside `tcp_vlg_sack`),
- keeps track of Acknowledgement number and SACK blocks,
- generates Forced Ack packets (pure Ack packets with no payload);

The incoming data if received out of order may be stored as SACK blocks in receive queue RAM. These SACK blocks are 'released' to user logic as soon as the missing segment arrives, filling the gap between last acknowledged byte (local Acknowledgement number) and left edge of that SACK block. When receving an in order packet (that has sequence number equal to local ack),`tcp_rx_ctl` will update local Acknowledgement number. This update corresponds to amount of bytes released from queue to user and the minimum amount of bytes released is the packet's length. However, each time a packet is received, `tcp_vlg_sack` will check local SACK blocks if they immedeately 'follow' this in order packet and may be released to user. Note that the data is released to user only at reception of an in order packet. 

## TCP transmit control
TCP transmit control is in charge of these functions:
- implements retransmission queue for outgoing data,
- assembles user stream to packets, calculates packet's checksum, sequence number,
- handles retransmission logic: timeouts

Unlike receive control which has only one RAM (receive data queue), the transmit control has two types of RAM served by logic. It also implements 3 FSMs: one for adding individual packets for 1st port `new_pkt` of packet information RAM referenced as `info`


 transmission queue of the TCP connection. `tcp_tx_ctl` aquires data directly from user logic, and stores, transmits or retransmits it. `tcp_tx_ctl` contains two types of RAM: packet information (i.e.: packet's sequence number, )
- `tcp_vlg_tx_ctl` is the transmission control block. It holds TCP transmission buffer data and handles retransmission events, 
## TCP engine
TCP engine contains the main TCP state machine. `tcp_vlg_engine` is responsible for main TCP logic: connection establishment, termination and events. Events are generated in `tcp_vlg_evt` by using timers and keeping track of incoming packets.
User has control over TCP via `tcp_ctl` interface direcrly wired to `tcp_vlg_engine` and may set local and remote port (in case of active connection), start listening (passive or server mode) or try to establish a connection (active or clinet mode) to a specified IP, abort connection and monitor connection status.
epending on whether the server was listening (waiting for SYN packet) or connecting actively by sending SYN packet to a specified ip:port pair, connection will be performed differently as a server or client. The signals to control TCP are presented in `tcp_ctl` interface.
Either way, while performing the TCP three-way-handshake THS, a Transmission Control Block structure `tcb` is generated by `tcp_vlg_engine`, sequence number is initialized in `tcp_tx_ctl` and acknowledgement number in `tcp_rx_ctl` by `tcp_vlg_engine`. When preforming the THS, TCB is filled with ports, IP and MAC addresses for future reference, sequence number is generated by a pseudo-random number generator and acknowledgement number is derived from remote seq. After the main FSM results in established state, local Seq and Ack numbers begin to update from `tcp_tx_ctl` and `tcp_rx_ctl` respectively. 
Data is transferred with a seperate `tcp_data` interface. 
### Transmission Control Block
Transmission Control Block `tcb` is a struct of type `tcb_t` described in `tcp_vlg_pkg`. It contatins infrormation on current connection:
- Local TCP port,
- Remote TCP port and IP address,
- Local Ack and Seq numbers,
- Last updated remote Ack and Seq numbers,
- Whether remote MAC is known (to skip ARP);

### Acknowledgment control
Acknowledgement control instantiated in `rx_ctl` is responsible for reporting successfully received data to remote host by generating pure acks (those with zero payload). The logic supports delayed acknowldegment and skips pure acks if actual ack number was already reported together with payload. The logic 

These three modules compose the TCP engine logic. `tcp_engine` is connected to `tcp_vlg_rx` and `tcp_vlg_tx`.

### tcp_vlg

`tcp_vlg` contains all logic responsible for TCP operation. It consists of several modules:
- `tcp_vlg_rx` Receiver handler. Parses incoming packets
- `tcp_vlg_tx` Transmit handler. Composes packets to transmit
- `tcp_vlg_tx_buff` is responsible for retransmission logic and pld checksum calculation. It stores raw TCP data from user logic in 8-bit RAM. Information such as length, sequence number and checksum is stored for each packet in a seperate `pkt_info` RAM. Information stored also includes retransmission-specific information. When a new packet is pending for transmission, space in allocated in transmission buff data RAM and a corrseponding entry is created in info RAM with all necssary information. The latter RAM is constantly scanned through and logic keeps track of unacked packets and tries to retransmit them after time based on TCP_RETRANSMIT_TICKS. `tcp_vlg_tx_buff` also generates a cts signal. The cts logic allows user to stop data strm 1 tick after ctr goes low to avoid data loss (or wiring cts signal to user logic instead of using a trigger).
- `tcp_vlg_server` TCP core. The state machine here handles connection establishment, and termination. The user control interface is implemented here described in Table 2.  Depending on run-time signals `connect` and `listen`, server can connect by IPv4 or listen for incoming connection.

### Server logic

After reset, the FSM is in idle state. Asserting `listen` signal will transition to a state which listens to incoming connection, that is, a packet with SYN flag set targeting local TCP port. Asserting `connect` signal will generate a TCP packet targeting `rem_port` TCP port and `rem_ipv4` IPv4 address. After either signal is asserted, a structure called *Transmission Control Block* or *TCB* is filled with information about connection being created.
After successfully performing the three-way handshake, the FSM results is in *connected* state in which data transfer takes place.
TCB rem_ack and rem_seq are being updated with TCP packets received and loc_ack and loc_seq are being updated from internal logic.

### Transmission buff and retransmissions
```
           _   _   _   _  //   _  //_   _   _
   clk   |/ \_/ \_/ \_/ \_//\_/ \_// \_/ \_/  
         |         ___    //      //
  send   | _______/   \___//______//_________ 
         |       (1)______//______//_
  pend   | _______/       //      // (4)_____ sets pending flag 
         | ___________    //    __//_________
  tx_idle|           (2)__//__(3) //
```
// (1): scan fsm decides to transmit a packet by asserting send for 1 tick
//      note that scan fsm may generate send event only if tx is idle
//      tx_arb takes care of waiting for other logic to finish transmitting their packets before actually sending this one
// (2): tx_idle goes low indicating that transmission just started. it will be held low until tx_arb reports that packet has been fully transmitted
// (3): tx_idle goes high after receiving ctl.sent
// (4): scan fsm searches for an entry with 'pend' flag set (i.e. a packet that was just sent)
//      and resets the 'pend' flag in packet's entry AND local pend signal that, when high, was blocking packets from being transmitted

// this mechanism is introduced to seperate scanning logic and transmission logic 
// so scanning and subsequent rto increments will be independent of transmitting possibly long packets making those timers accurate
// it is also made to transmit packets in order, i.e. when tx_idle goes high, the FSM won't send just any packet ready for transmission
// in queue that was being checked, but instead will return to address that triggered that transmission
// and will check exactly the next packet for possible retransmission meaning in-order retransmissions!

////////////////////
// Scanning logic //
////////////////////

//
//_______________________________________
//____[?????[=====SACK=====]?????]_______
//       [====================]
//       ^                    ^
//       upd_pkt.start        upd_pkt.stop
// the idea is to scan the info RAM entries by iterating upd_ptr.
// only packets with present flag set may be transmitted,
// packets without present flag are not considered
// the choice on what to do with the packet is made in choice_s.
// - the logic will free the packet if remote ack covers all bytes in it
// - a normal retransmission (which should ideally never trigger due to highest delay of RETRANSMIT_TICKS)
// - a fast retransmission if dup acks were detected (skip retransmission rto) which is reported by fast_rtx module via tx_ctl interface (it's named ctl local)
// - a sack generated retransmission immediately 
// there are two retransmission timers  
TCP receiver does not need to acknowledge each packet, instead it may cknowledge multiple packets if all were received successfully. This implies that sender stores all unacknowledged data and may retransmit unacknowledged packets.
Transmission buff stores user data in an 8-bit RAM which is filled with new user data and freed as remote acknowledge progresses. A seperate `pkt_info` RAM is also filled with information about each packet when it is formed: sequence number, length and checksum as well as retransmission timer and retransmissions count. After being formed, the packets may only be transmitted as written without the ability to split and/or combine them. This limitation is imposed to avoid recalculating TCP pld checksum. There are several conditions in which the packet is considered complete and is buffd for transmission:
- Data RAM full;
- MSS reached;
- No new data for TCP_TX_TIMEOUT ticks (default: 50);
- Packet forced to be buffd without waiting for TCP_TX_TIMEOUT by asserting `tcp_snd`.

buff's FSM continiously scans `pkt_info` RAM for entries with `present` flag set. This flag indicates that a packet is still stored in data RAM because it is not acked by the receiver yet. After finding and entry with `present` flag set, the buff FSM processes the packet in one of the following ways:
- Packet's *sequence* number plus packet's *length* is **less or equal** than remote *acknowledgment* number indicates that packet is acked. Present flag will be cleared releasing space for next packets in data RAM and `pkt_info` RAM.
- Packet's *sequence* number plus packet's length **higher** than remote *acknowledgment* number and retransmit timer less than timeout value indicates that packet is yet unacknowledged, but there is still time for remote device to acknowledge it before retransmission occurs. Retransmit timer is incremented and next packet is processed.
- Packet's *sequence* number plus packet's *length* **higher** than remote *acknowledgment* number and *retransmit timer* **equal** to *timeout* value indicates that packet is unacknowledged and retransmission timeout is reached. Retransmission occurs, number of *retransmission tries* is incremented and *retransmit timer* is reset to zero. Note that when a new entry is created, retransmit timer is preloaded with timeout value, so the first time a new packet is transmitted without waiting for retransmission timeout.
- Packet's *retransmission tries* reaching retransmission limit will trigger forced connection termination.

Transmission buff is directly wired to user transmission logic with `tcp_din`, `tcp_vin`, `tcp_cts` and `tcp_snd`.
