## Synthesys source files
The files in this folder together with `hdl_generics/src` are used for synthesys. The tools have to correctly process structs, typedefs and interfaces modports. For more detailed description on each protocol implementation, refer to readme files in corresponding folders.
## eth_vlg block scheme
```         
                                                           ╔ICMP╗
                                                           ╟────╢
                                                       ┌──►║ rx ║
                                                       │   ╟────╢
                                                       │ ┌─╢ tx ║
                                                       │ │ ╚════╝
                                                       │ │ ╔═UDP═╗  ╔═DHCP═╗
                                        ╔═IPv4═════╗   ├─│►║ rx  ╟─►║  rx  ║
                 ╔═MAC══════════╗       ║          ║   │ │ ╟─────╢  ╟───▼──╢
         ╔DDR╗   ╟────┐         ║       ╟────┐     ║   │ │ ║     ║  ║ core ╟─► set local ip
from phy ╫───╫───╢ rx ├─────────╫──┬───►║ rx ├─────╫───┤ │ ╟─────╢  ╟───▼──╢
         ║   ║   ╟────┘         ║  │    ╟────┘ ┌───╢  ┌│─│─╢ tx  ║◄─╢  tx  ║
         ║   ║   ║      ┌───────╢  │    ╟────┐ │   ║◄─┘│ │ ╚═════╝  ╚══════╝
         ║   ║   ╟────┐ │  mux  ║◄─│────╢ tx │◄┤mux║◄──│─┘ ╔═TCP═══════════════╗  ╔══user logic═══
  to phy ╫───╫───╢ tx │◄┤       ║◄┐│    ╟────┘ │   ║◄┐ │   ╟────┐    ┌──core──┐║  ║
         ╚═══╝   ╟────┘ └───────╢ ││    ║      └───╢ │ └──►║ rx ├─┬─►│ rx_ctl─┼╫─►║raw tcp rx
       (optional)╚══════════════╝ ││    ╚══════════╝ │     ╟────┘ │  ├────↕───┤║  ║
                                  ││ ╔═ARP══════════╗│     ║      └─►│ engine◄┼╫─►║status & control
                                  ││ ╟────┐ ┌───────╢│     ╟────┐    ├────↕───┤║  ║
                                  │└►║ rx ├►│       ║└─────╢ tx │◄───┤ tx_ctl◄┼╫──║raw tcp tx
                                  │  ╟────┘ │       ║      ╟────┘    └────────┘║  ║
                                  │  ╟────┐ │ table ║      ╚═══════════════════╝  ╚═══════════════
                                  └──╢ tx │◄┤       ║
                                     ╟────┘ └───────║
                                     ╚══════════════╝
```
## Architecture overview
The main idea is to split logic by protocol handlers in a way that they appear as "black boxes" to each other and interact with compact and uniform interfaces. Each handler is responsible for corresponding protocol's logic. These handlers always have at least a top level module, packet parser (notated as `_rx`) and packet assembler (`_tx`). A minimalistic example is `icmp`. Depending on the protocol, handlers need to support that protocol's specific logic. Handlers communicate with each other mainly by means of interfaces named by the protocol they carry (exception is the IPv4's usage of ARP). These interfaces contain payload stream `strm` and metadata information `meta` for receve and transmit paths and several additional signals for transmit path. These additional signals are used to manage multiple trasnmissions by multiple handlers connected to a single one.
## Receive path
Packet reception is composed of three main operations: 
- parse header by protocol, inform subseqent logic (`_rx`),
- pass payload to subsequent logic as stream of words (`_rx`),
- perform specific operations when a certian packet arrives (`rx_ctl`)
The output interface of the receive part of a specific handler is compsed of 
```
┌────────┬─────────┐
| header | payload |
└────┬───┴────┬────┘╔interface╗
     |        └────►║  strm   ║
     └─────────────►║  meta   ║
                    ╚═════════╝
┬───┬───┬───┬
|src|dst|eth| 
|mac|mac|typ| 
┴───┴───┴───┴

```
## Transmit path
### Transmit path signals
### Transmit path multiplexer
While strm interface is common between all payload-ontaining protocols
A similar interface is used to communicate between handlers and it consists of 'strm' (stream) of payload which is common between all handlers as it's just a stream of payload bytes and protocol-specific 'meta' (metadata) which is exctracted from/converted to that protocol's header. 'strm' will carry the protocol's payload as a stream of bytes for further processing while 'meta' will carry relevant header data. Some handlers are easy to implement, others require additional logic. For example, MAC requires FCS computation, ARP has a RAM table to store entries and TCP needs flow control and an engine.


