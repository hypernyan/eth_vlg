## Synthesys source files
The files in this folder together with `hdl_generics/src` are used for synthesys. 
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
 ╟────┐         ║       ╟────┐     ║   │ │ ║     ║  ║ core ╟─► set local ip
 ║ rx ├─────────╫──┬───►║ rx ├─────╫───┤ │ ╟─────╢  ╟───▼──╢
 ╟────┘         ║  │    ╟────┘ ┌───╢  ┌│─│─╢ tx  ║◄─╢  tx  ║
 ║      ┌───────╢  │    ╟────┐ │   ║◄─┘│ │ ╚═════╝  ╚══════╝
 ╟────┐ │  mux  ║◄─│────╢ tx │◄┤mux║◄──│─┘ ╔═TCP═══════════════╗  ╔══user logic═══
 ║ tx │◄┤       ║◄┐│    ╟────┘ │   ║◄┐ │   ╟────┐    ┌──core──┐║  ║
 ╟────┘ └───────╢ ││    ║      └───╢ │ └──►║ rx ├─┬─►│ rx_ctl─┼╫─►║raw tcp rx
 ╚══════════════╝ ││    ╚══════════╝ │     ╟────┘ │  ├────↕───┤║  ║
                  ││ ╔═ARP══════════╗│     ║      └─►│ engine◄┼╫─►║status & control
                  ││ ╟────┐ ┌───────╢│     ╟────┐    ├────↕───┤║  ║
                  │└►║ rx ├►│       ║└─────╢ tx │◄───┤ tx_ctl◄┼╫──║raw tcp tx
                  │  ╟────┘ │       ║      ╟────┘    └────────┘║  ║
                  │  ╟────┐ │ table ║      ╚═══════════════════╝  ╚═══════════════
                  └──╢ tx │◄┤       ║
                     ╟────┘ └───────║
                     ╚══════════════╝
```
The main idea is to split logic by protocol handlers in a way that they appear as "black boxes" to each other. Each handler is designed to attach a protocol-specific header when assembling a packet for transmission or remove the header from a packet when receiving. Additional logic is provided if necessary. A similar interface is used to communicate between handlers and it consists of 'strm' (stream) of payload which is common between all handlers as it's just a stream of payload bytes and protocol-specific 'meta' (metadata) which is exctracted from/converted to that protocol's header. 'strm' will carry the protocol's payload as a stream of bytes for further processing while 'meta' will carry relevant header data. Some handlers are easy to implement, others require additional logic. For example, MAC requires FCS computation, ARP has a RAM table to store entries and TCP needs flow control and an engine.


