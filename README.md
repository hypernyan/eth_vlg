# eth_vlg

TCP/IP stack implemented in SystemVerilog
Protocols implemented: ARP, IPv4 (ICMP, UDP and TCP)  
Features:
- Connect to a host with an IPv4 or wait for the first client to connect
- Retransmission logic: bufferize user tx data, hold it until acknowledgement. 
- ARP table: hold IPv4/MAC pairs for multiple hosts
- ARP requests: generate ARP request if no entry found
Drawbacks:
- No PRBS generated ISN
- No SACK
- 
Brief explaination:
Protocol-specific headers are generated and parseed by _tx and _rx notated modules.
The extract data from headers or generate headers based on underlying protocol's data.
For example, IPv4 needs Ethertype which is contained in MAC layer header