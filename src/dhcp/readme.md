# DHCP

The DHCP client offers automatic control of IP lease aqcuisition and prolongation as well as automatic release if IP if user desires to acquire new one.

The DHCP client has two state machines: control logic described in `dhcp_vlg_ctl` and message handler `dhcp_vlg_msg`. 

Control FSM is responsible for acquiring IP lease, renewing and rebinding and managing lease timer. It is this module that is connected to user control interface that is brought up to `eth_vlg` top level.

Message FSM encapsulates communication with DHCP server. It generates messaged for `dhcp_vlg_tx` and processes data received by `dhcp_vlg_rx`. The Message FSM handles message timeouts. It receives control signals from Control FSM:

- init
- renew
- rebind
- releas

And automatically performs necessary message exchange with the DHCP server via `dhcp_vlg_rx` and `dhcp_vlg_tx` while signaling the Control FSM whether the operation requested by the Control FSM was successful.

`init` `renew` and `rebind` operations are considered successful if `DHCPACK` message was eventually received from the DHCP server. `releas` operation does not require acknowledge from the server and thus considered successful upon sending `DHCPRELEASE` message to the DHCP server. 
  
While `init` operation is considered failed after `DHCP_RETRIES` tries each lasting `DHCP_TIMEOUT_SEC` seconds, the `renew` and `release` do not have a timeout. Instead, `renew` and `release` are considered failed if lease could not be prolonged by the DHCP server by the DHCP lease time negotiated during `init` stage.

# User interface
