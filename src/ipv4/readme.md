## IPv4

`ipv4_vlg_top` module contains ipv4 related logic including ICPM, UDP and TCP. ipv4\_vlg\_top directly interfaces user logic with raw TCP streams and TCP control/status ports.
`ipv4_vlg_top` transmission logic is based on buf_mng arbiter module which asynchronously receives packets from ICMP, UDP and TCP and buffs them for transmission to MAC.
