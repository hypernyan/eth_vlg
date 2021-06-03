    ## Synthesys source files
    
    ## Overall architecture
    ```
                  ╔═══╗
                  ║TCP       ║
               ┌─►║rx        ║─►
               │  ╚═══╝   
               
               
               
               
  ╔═════╗            ╔════════╗   ╔════╗
  ║ MAC ║            ║IPv4 top║   ║UDP ║     ╔═══╗   ╔════╗
  ╟─────╢            ╟────╢   ║    ║◄─►║DHCP║
  ║     ╟───────────►║ rx ╟──►╟ rx   ╢   ╟    ╢
  ║ rx  ║            ╟    ────╢          rx
  ╟─────╢ ╔═══════╗◄─╢     tx ║
  ║ tx  ║◄╢mac mux║  ╚════════╝   ╚═══╝   ╚════╝    
  ╚═════╝ ╚═══════╝◄┐             
                    │╚═▲══════╝         ╔════╗
    ╔═══╗           │          icmp
    ║ARP║           │
                    │
                    │
     tx  ───────────┘
    ╚═══╝
  
 
    ```
    
    
    The main idea is to split logic by protocol handlers in a way that they appear as "black boxes" to each other. each handler will attach a protocol-specific header when assembling a packet for transmission or remove the header from a packet when receiving. A similar interface is used to communicate between handlers and it consists of 'strm' (stream) of payload and 'meta' (metadata) which was exctracted from/will be converted to that protocol's header. 'Strm' will carry the protocol's payload as a stream of bytes for further processing while 'meta' will carry relevant header data.

    TCP overall logic
    The TCP logic consists of multiple modules: the tcp_vlg_rx and tcp_vlg_tx are receive and transmit handlers. They only receive/transmit IPv4 packets and extract metadata from TCP header. These handlers are a bit more complex then most other handlers as they have to deal with variable TCP options.
    TCP core:
    The TCP core is responsible for TCP logic including rx and tx queues, the main FSM (engine), transmissions and other
    The core itself is composed of TCP engine, receive and transmit control.
    TCP Engine:
    This module contains the main TCP state machine responsible for connection establishment/termination and updating fields in TCB structure.
    The state machine is controlled by user
    Connection establishment:
    The connection may be established in two ways: active (client) or passive (server). After the three-way-handshake is complete

