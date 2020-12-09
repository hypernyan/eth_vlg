set SHOW_TOP  0
set SHOW_MAC_CLI          1
set SHOW_MAC_SRV          0
set SHOW_ARP              0

set SHOW_IP_CLI           1
set SHOW_ICMP_CLI         1
set SHOW_TCP_CLI          1
set SHOW_TCP_ENGINE_CLI   0
set SHOW_TCP_TX_QUEUE_CLI 0
set SHOW_TCP_RX_CLI       0
set SHOW_TCP_TX_CLI       1
set SHOW_UDP_CLI          1
set SHOW_DHCP_CLI         1

set SHOW_IP_SRV           0
set SHOW_ICMP_SRV         0
set SHOW_TCP_SRV          0
set SHOW_TCP_ENGINE_SRV   0
set SHOW_TCP_TX_QUEUE_SRV 0
set SHOW_TCP_RX_SRV       0
set SHOW_TCP_TX_SRV       0
set SHOW_DHCP_SRV         0

onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider -height 40 {switch}
add wave -noupdate -format Logic -radix hexadecimal {tb/switch_sim_inst/*}
add wave -noupdate -divider -height 40 {gateway}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/*}
add wave -noupdate -divider -height 20 {in}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/in/*}
add wave -noupdate -divider -height 40 {out}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/out/*}

add wave -noupdate -divider -height 40 {TESTBENCH}
add wave -noupdate -format Logic -radix hexadecimal {tb/*}

add wave -noupdate -divider -height 20 { ////////////////// }
add wave -noupdate -divider -height 20 { ///// CLIENT ///// }
add wave -noupdate -divider -height 20 { ////////////////// }

#===============================================
if {$SHOW_MAC_CLI == 1} {
    add wave -noupdate -divider -height 20 {MAC}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -divider -height 20 {mac rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {mac rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/*}
    add wave -noupdate -divider -height 20 {mac rx fcs}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/crc32_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/d}
}

if {$SHOW_IP_CLI == 1} {
    add wave -noupdate -divider -height 20 {Client IPv4 top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {Client IPv4 top mux}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_tx_mux_isnt/*}
    add wave -noupdate -divider -height 20 {Client IPv4 top mux interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_tx_mux_isnt/ipv4/*}
    add wave -noupdate -divider -height 20 {Client IPv4 rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {Client IPv4 rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {Client IPv4 tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {Client IPv4 tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/ipv4/*}
}

if {$SHOW_ICMP_CLI == 1} {
    add wave -noupdate -divider -height 20 {Client ICMP}
    add wave -noupdate -divider -height 20 {Client ICMP rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {Client ICMP tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_tx_inst/*}
}

if {$SHOW_TCP_RX_CLI == 1} {
    add wave -noupdate -divider -height 20 {Client TCP rx}

    add wave -noupdate -divider -height 20 {IPv4 in}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_rx_inst/ipv4/*}

    add wave -noupdate -divider -height 20 {TCP out}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_rx_inst/tcp/*}
}

if {$SHOW_TCP_TX_CLI == 1} {
    add wave -noupdate -divider -height 20 {Client TCP tx}
    add wave -noupdate -divider -height 20 {IPv4 out}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {TCP in}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/tcp/*}
    add wave -noupdate -divider -height 20 {Logic}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/*}
}

if {$SHOW_TCP_ENGINE_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP Engine}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/rst}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/tcp_fsm}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/connect}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/connected}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/listen}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/listen}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/connection_type}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/force_fin}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/close}
    add wave -noupdate -divider -height 20 {queue}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/queue/*}
    add wave -noupdate -divider -height 20 {checksum}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/hdr_calc}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/pseudo_hdr}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/chsum_carry}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/hdr_chsum}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/calc_cnt}
}

if {$SHOW_TCP_TX_QUEUE_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP TX Queue Client}

    add wave -noupdate -divider -height 20 {Client Queue}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_queue_inst/*}
    add wave -noupdate -divider -height 20 {Queue RAM}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_queue_inst/tcp_data_queue_inst/*}
}
if {$SHOW_UDP_CLI == 1} {
    add wave -noupdate -divider -height 20 {UDP top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {UDP Client rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {UDP Client rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/udp/*}
    add wave -noupdate -divider -height 20 {UDP Client tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {UDP Client tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/udp/*}
}
if {$SHOW_DHCP_CLI == 1} {
    add wave -noupdate -divider -height 20 {Client: DHCP top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {Client: DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_rx/*}
    add wave -noupdate -divider -height 20 {Client: DHCP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_tx/*}
    add wave -noupdate -divider -height 20 {Client: DHCP UDP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/rx/*}
    add wave -noupdate -divider -height 20 {Client: DHCP DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_rx/*}
    add wave -noupdate -divider -height 20 {Client: DHCP UDP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/tx/*}
        add wave -noupdate -divider -height 20 {Client: DHCP DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_tx/*}
    add wave -noupdate -divider -height 20 {Client: DHCP core}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_core_inst/*}
    add wave -noupdate -divider -height 20 {Client: DHCP rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {Client: DHCP tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {Client: DHCP tx string handler}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_tx_inst/string_handler_hostname_inst/*}
}

if {$SHOW_UDP_CLI == 1} {
    add wave -noupdate -divider -height 20 {Client: UDP}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/*}

    add wave -noupdate -divider -height 20 {Client: UDP RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {Client: UDP IPv4 interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {Client: UDP UDP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/udp/*}

    add wave -noupdate -divider -height 20 {Client: UDP TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {Client: UDP IPv4 interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {Client: UDP UDP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/udp/*}
}

#===============================================

if {$SHOW_IP_SRV == 1} {
    add wave -noupdate -divider -height 20 {IP Server}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {IP Server RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {IP Server TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
}
#===============================================

if {$SHOW_ICMP_SRV == 1} {

    add wave -noupdate -divider -height 20 {ICMP Server}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_tx_inst/*}
}
#===============================================

if {$SHOW_TCP_TX_QUEUE_SRV == 1} {
    add wave -noupdate -divider -height 20 {Server Queue}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_tx_queue_inst/*}
    add wave -noupdate -divider -height 20 {Queue RAM}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_tx_queue_inst/tcp_data_queue_inst/*}
}

if {$SHOW_TCP_RX_SRV == 1} {
    add wave -noupdate -divider -height 20 {TCP Rx Srv}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_rx_inst/*}
}

if {$SHOW_TCP_TX_SRV == 1} {
    add wave -noupdate -divider -height 20 {TCP Tx Srv}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/*}
}

if {$SHOW_UDP_SRV == 1} {
    add wave -noupdate -divider -height 20 {Client: UDP}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/udp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {Client: UDP RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst}
    add wave -noupdate -divider -height 20 {Client: UDP TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst}
}

#===============================================
if {$SHOW_ARP == 1} {
    add wave -noupdate -divider -height 40 {ARP CLI}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_vlg_tx_inst/*} 
    add wave -noupdate -divider -height 40 {ARP Table}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_table_inst/*} 
    add wave -noupdate -divider -height 40 {ARP SRV}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/arp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/arp_vlg_inst/arp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/arp_vlg_inst/arp_vlg_tx_inst/*} 
    add wave -noupdate -divider -height 40 {ARP Table}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/arp_vlg_inst/arp_table_inst/*} 
}

TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
configure wave -namecolwidth 201
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
update
