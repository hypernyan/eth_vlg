# UDP
UDP is used by DHCP at initializtion in order to aquire IP address from DHCP server. After DHCP's DORA sequence has either succeeded or failed, UDP becomes available for user. UDP is configured via `udp_ctl` interface. Information on source of UDP frame: ip address and port are also provided via this interface.
## Receive
Receive logic is straightforward: no buffer is present as no receive queue is necessary for UDP (unlike TCP) and there is no mechanism to indicate lost or out-of-order frames. UDP payload will be streamed in `udp.out_rx` interface if source IP and port match those set in `dev` structure and `ctl` interface.
## Transmit
Transmission logic 