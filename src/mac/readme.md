# MAC
MAC interfaces PHY outside the FPGA with a GMII interface. It interfaces ARP and IPv4 logic with `mac` interface. `phy` and `mac` interfaces are defined in `eth_vlg_if.sv` and `mac_vlg_if` accordingly. The logic supports RGMII by default. RGMII is currently supported out of box for Intel FGPA (Cyclone 10 LP hardware verified). The DDR registers and PLLs for phase shift are instantiated in `vendors/rgmii_adapter.sv` while constraints are set in `constraints'sdc`. The logical schematic of `mac_vlg` is presented below:
```
            +-----------------------------+  
            | mac_vlg                     |  
+-------+   | +-----------+  +----------+ |  
|       | ===>|mac_vlg_cdc|=>|mac_vlg_rx|===> To ARP and IPv4 rx
| RGMII |   | +-----------+  +----------+ | 
|adapter|   |                +----------+ |
|       | <==================|mac_vlg_tx|<=== From ARP and IPv4
+-------+   |                +----------+ |
            +-----------------------------+  
```
## Receive
### `mac_vlg_cdc`
Receive path starts with clock domain crossing handled by `mac_vlg_cdc`. A dual-clock fifo is used for this purpose as it introduces a dual-port RAM. In case phy 125MHz receive clock generated by PHY IC is a bit slower than the local 125MHz clock, to eliminate chance of packed valid signal disruption, `mac_vlg_cdc` logic waits for a few bytes to stack in FIFO's RAM befor passing it to local clock domain. The delay imposed is parametrized by `DELAY` parameter.
### `mac_vlg_rx`
When receiving a packet, `mac_vlg_rx` checks for correct preamble and delimiter. After that, if the packet's destination MAC is equal to local MAC set by the `MAC_ADDR` parameter or if it's broadcast (xFF:...), `mac_vlg_rx` fills the `mac_hdr` fields inside `meta` structure: `dst_mac`, `src_mac`, `ethertype`. The logic also passes packet's length to subsequent logic. Payload is stripped from Ethernet header and FCS and passed to ARP and IPv4 within `strm` stream interface. `strm` consists of four signals: `dat`, `val`, `sof` and `eof`. The packet is assumed to be complete as soon as current calculated CRC equals CRC magic number. No special arbitration is needed between MAC and subsequent IPv4 and ARP protocols, they both receive same data in parallel. Either protocol handlers are triggered based on Ethertype passed by MAC. 
## Transmit
### `mac_vlg_tx`
The transmit part of MAC adds everything needed to form an Ethernet frame: preamble, Ethernet header and FCS. `eth_vlg_tx_mux` is used to multiplex ARP and IPv4 transmit logic. FCS is computed and appended as the packed is generated and passed to `rgmii_adapter`