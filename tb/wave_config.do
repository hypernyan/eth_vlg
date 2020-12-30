set SHOW_TOP  0
set SHOW_MAC_CLI          0
set SHOW_MAC_SRV          0
set SHOW_ARP              0


set SHOW_MAC_RX_CLI       1
set SHOW_MAC_TX_CLI       1
set SHOW_MAC_TX_PHY_CLI   1
set SHOW_MAC_TX_MUX_CLI   1

set SHOW_IP_TOP_CLI       0
set SHOW_IP_RX_CLI        1
set SHOW_IP_TX_CLI        1
set SHOW_IP_TX_MUX_CLI    1

set SHOW_ICMP_CLI         0

set SHOW_TCP_CLI          0
set SHOW_TCP_ENGINE_CLI   1
set SHOW_TCP_TX_QUEUE_CLI 0
set SHOW_TCP_RX_CLI       1
set SHOW_TCP_TX_CLI       1

set SHOW_ARP_CLI          1
set SHOW_ARP_TABLE_CLI    1
set SHOW_ARP_TX_CLI       1
set SHOW_ARP_RX_CLI       1

set SHOW_UDP_CLI          0
set SHOW_DHCP_CLI         0

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

add wave -noupdate -divider -height 40 {***switch***}
add wave -noupdate -format Logic -radix hexadecimal {tb/switch_sim_inst/din}
add wave -noupdate -format Logic -radix hexadecimal {tb/switch_sim_inst/vin}
add wave -noupdate -format Logic -radix hexadecimal {tb/switch_sim_inst/dout}
add wave -noupdate -format Logic -radix hexadecimal {tb/switch_sim_inst/vout}
add wave -noupdate -divider -height 40 {***gateway***}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/receiving}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/send}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/fsm_rx}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/fsm_tx}
add wave -noupdate -divider -height 20 {in}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/in/dat}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/in/val}
add wave -noupdate -divider -height 20 {out}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/out/dat}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/out/val}

add wave -noupdate -divider -height 40 {TESTBENCH}
add wave -noupdate -format Logic -radix hexadecimal {tb/*}

add wave -noupdate -divider -height 20 {CLIENT}

if {$SHOW_MAC_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli mac}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/*}
}
if {$SHOW_MAC_TX_PHY_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli mac phy}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/*}
}
if {$SHOW_MAC_TX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli mac tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {cli mac fcs}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/crc32_inst/*}
    add wave -noupdate -divider -height 20 {cli mac interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/mac/*}
}
if {$SHOW_MAC_RX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli mac rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {cli mac fcs}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/crc32_inst/*}
    add wave -noupdate -divider -height 20 {cli mac rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/*}
}
if {$SHOW_MAC_TX_MUX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli mac tx mux}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/eth_vlg_tx_mux_inst/*}
}
if {$SHOW_IP_TOP_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli ipv4 top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/*}
}
if {$SHOW_IP_RX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli ipv4 rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {cli ipv4 rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {cli ipv4 tcp rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/tcp/*}
}
if {$SHOW_IP_TX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli ipv4 tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {cli ipv4 tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {cli ipv4 mac tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/mac/*}
}
if {$SHOW_IP_TX_MUX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli ipv4 tx mux}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/eth_vlg_tx_mux_isnt/*}
}
if {$SHOW_ICMP_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli ICMP}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/*}
}
if {$SHOW_ICMP_RX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli ICMP rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_rx_inst/*}
}
if {$SHOW_ICMP_TX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli ICMP tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_tx_inst/*}
}
if {$SHOW_TCP_RX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli TCP rx}

    add wave -noupdate -divider -height 20 {ipv4 in}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_rx_inst/ipv4/*}

    add wave -noupdate -divider -height 20 {TCP out}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_rx_inst/tcp/*}
}
if {$SHOW_TCP_TX_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli TCP tx}
    add wave -noupdate -divider -height 20 {ipv4 out}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {TCP in}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/tcp/*}
    add wave -noupdate -divider -height 20 {Logic}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/*}
}
if {$SHOW_TCP_ENGINE_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP Engine}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/*}
    add wave -noupdate -divider -height 20 {TCP Engine tcp tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_engine_inst/tx/*}
}
if {$SHOW_TCP_TX_QUEUE_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP TX Queue cli}

    add wave -noupdate -divider -height 20 {cli Queue}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_queue_inst/*}
    add wave -noupdate -divider -height 20 {Queue RAM}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_queue_inst/tcp_data_queue_inst/*}
}
if {$SHOW_UDP_CLI == 1} {
    add wave -noupdate -divider -height 20 {UDP top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {UDP cli rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {UDP cli rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/udp/*}
    add wave -noupdate -divider -height 20 {UDP cli tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {UDP cli tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/udp/*}
}
if {$SHOW_DHCP_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli: DHCP top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_rx/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_tx/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP UDP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/rx/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_rx/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP UDP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/tx/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_tx/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP core}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_core_inst/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_rx_inst/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_tx_inst/*}
    
    add wave -noupdate -divider -height 20 {cli: DHCP tx udp interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_tx_inst/udp/*}
}
if {$SHOW_UDP_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli: UDP}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/*}

    add wave -noupdate -divider -height 20 {cli: UDP RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/*}
    
    add wave -noupdate -divider -height 20 {cli: UDP ipv4 interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/ipv4/*}
    
    add wave -noupdate -divider -height 20 {cli: UDP UDP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/udp/*}

    add wave -noupdate -divider -height 20 {cli: UDP TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/*}
    
    add wave -noupdate -divider -height 20 {cli: UDP ipv4 interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/ipv4/*}
    
    add wave -noupdate -divider -height 20 {cli: UDP UDP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/udp/*}
}

if {$SHOW_ARP_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli arp}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/*}
}
if {$SHOW_ARP_RX_CLI == 1} {   
    add wave -noupdate -divider -height 20 {cli arp rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_vlg_rx_inst/*}
}
if {$SHOW_ARP_TX_CLI == 1} {   
    add wave -noupdate -divider -height 20 {cli arp tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_vlg_tx_inst/*} 
    add wave -noupdate -divider -height 20 {cli arp tx mac interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_vlg_tx_inst/mac/*} 
        
}
if {$SHOW_ARP_TABLE_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli arp table}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_table_inst/*} 
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
    add wave -noupdate -divider -height 20 {cli: UDP}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/udp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {cli: UDP RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst}
    add wave -noupdate -divider -height 20 {cli: UDP TX}
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
