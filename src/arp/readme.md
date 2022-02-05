# ARP
ARP is responsible for binding IPv4 address with MAC. Knowing target IP address, one can acquire it's MAC with ARP. ARP is composed of several modules:
- `arp_vlg_rx` to parse ARP packets;
- `arp_vlg_tx` to generate ARP packets;
- `arp_table` to store IPv4/MAC pairs and generate ARP requests.
ARP will reply to requests automatically if  but it's also connected to IPv4. Each time IPv4 is generating a packet, it's logic makes a request to ARP. ARP then scans it's memory for requested IPv4 address and if such an entry isn't found, makes several attempts send ARP requests. If successfull, ARP returns target MAC to IPv4 transmission logic.

ARP in `eth_vlg` serves the following functions:
 - informs remote nodes of device MAC
 - captures and stores MAC-IPv4 pairs of remote nodes
 - Reports IPv4 tx logic with MAC of remote node if known
 - performs ARP requests for remote node's MAC as requested by IPv4 tx module
tperforms ARP requests for IPv4 tx 

ARP table
handles the table itself as well as requests for yet unknown remote nodes. 

IPv4 tx module shall normally request ARP module for MAC of the remote node to compose ethernet header needed for MAC tx. If, however, IPv4 tx module is broadcasting (destination IP is 255.255.255.255) or if it is told that MAC is known (MAC is then passed in ipv4 meta), it skips ARP interaction phase and continues directly to actual transmission.
In eth_vlg, TCP stores MAC of the remote node after receiving the first packet from that node and sets mac_known bit accordingly.

Two FSMs are present in ARP table module each interfacing one of the two ports of the dual-port ram containing MAC-IPv4 entries

The Write FSM `w_fsm` is responsible for handling writes to ARP table from received ARP packets. Both requests and replies are used to exctract the information about node's IPv4 and MAC, although only ARP packets dedicated to the local device node are used. ARP packets targeting other nodes are ignored to avoid ARP table overflow.

The Read FSM `r_fsm` is used in conjunction with IPv4 transmission logic `ipv4_vlg_tx` and is controlled by it's requests. Upon a newly issued request, r_fsm first scans the RAM. If an entry containing the requested IP is found, r_fsm replies to IPv4 tx with MAC from that entry. Otherwise, after scanning the whole table, it issues ARP requests to remote node. If ARP fails to receive reply in TIMEOUT ticks, it resends the requests for RETRIES amount of times in TIMEOUT intervals. If those fail too, IPv4 tx is being reported with err within the ARP-IPv4 tx interface.
