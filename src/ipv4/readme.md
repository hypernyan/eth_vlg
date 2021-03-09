## IPv4
Files contained in `/src/ipv4/` described  
The top level file `ipv4_vlg_top`. contains IPv4 and related handlers: logic responsible for IPv4 itself as well as ICMP, TCP, UDP and DHCP.
### Architecure
The ipv4 receive logic described in parses packets 
`ipv4_vlg_top` structure:
```
               +----+
               |dhcp|
               +--+-+
                  |
                +-+-+   +------+
             +->|udp|-->|      |
             |  +---+   |      |
+---------+  |  +---+   |      |  +---------+
| ipv4_rx |--+->|tcp|-->|tx_mux|->| ipv4_tx |
+---------+  |  +---+   |      |  +---------+
             |  +----+  |      |
             +->|icmp|->|      |
                +----+  +------+
```
`ipv4_vlg_top` module contains ipv4 related logic including ICPM, UDP and TCP. ipv4\_vlg\_top directly interfaces user logic with raw TCP streams and TCP control/status ports.
`ipv4_vlg_top` transmission logic is based on buf_mng arbiter module which asynchronously receives packets from ICMP, UDP and TCP and buffs them for transmission to MAC.
