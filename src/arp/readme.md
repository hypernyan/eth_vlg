# ARP
ARP is responsible for binding IPv4 address with MAC. Knowing target IP address, one can acquire it's MAC with ARP. ARP is composed of several modules:
- `arp_vlg_rx` to parse ARP packets;
- `arp_vlg_tx` to generate ARP packets;
- `arp_table` to store IPv4/MAC pairs and generate ARP requests.
ARP will reply to requests automatically if  but it's also connected to IPv4. Each time IPv4 is generating a packet, it's logic makes a request to ARP. ARP then scans it's memory for requested IPv4 address and if such an entry isn't found, makes several attempts send ARP requests. If successfull, ARP returns target MAC to IPv4 transmission logic.