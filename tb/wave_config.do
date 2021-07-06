set SHOW_TOP  0

set SHOW_MAC_CLI  0
set SHOW_ARP_CLI  0
set SHOW_IP_CLI   1
set SHOW_ICMP_CLI 0
set SHOW_TCP_CLI  0
set SHOW_UDP_CLI  0
set SHOW_DHCP_CLI 1

onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider -height 40 {***switch***}
add wave -noupdate -format Logic -radix hexadecimal {tb/switch_sim_inst/*}
add wave -noupdate -divider -height 40 {***gateway***}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/*}
add wave -noupdate -divider -height 20 {in}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/in/dat}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/in/val}
add wave -noupdate -divider -height 20 {out}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/out/dat}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/out/val}
add wave -noupdate -divider -height 20 {cli receiver}
add wave -noupdate -format Logic -radix hexadecimal {tb/receiver_cli_inst/*}
add wave -noupdate -divider -height 20 {srv receiver}
add wave -noupdate -format Logic -radix hexadecimal {tb/receiver_srv_inst/*}
add wave -noupdate -divider -height 20 {cli sender}
add wave -noupdate -format Logic -radix hexadecimal {tb/sender_cli_inst/*}
add wave -noupdate -divider -height 20 {srv sender}
add wave -noupdate -format Logic -radix hexadecimal {tb/sender_srv_inst/*}

add wave -noupdate -divider -height 40 {TESTBENCH}
add wave -noupdate -format Logic -radix hexadecimal {tb/*}
add wave -noupdate -divider -height 40 {CLI}
add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/*}
add wave -noupdate -divider -height 40 {CLI}
add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/tcp_ctl/*}
add wave -noupdate -divider -height 20 {CLIENT}


if {$SHOW_MAC_CLI == 1} {
    add wave -noupdate -divider -height 20 {[cli] mac}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/*}
    add wave -noupdate -divider -height 20 {[cli] mac tx phy interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/*}
    add wave -noupdate -divider -height 20 {[cli] mac rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] mac rx fcs}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/crc32_inst/*}
    add wave -noupdate -divider -height 20 {[cli] mac rx mac interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/*}
    add wave -noupdate -divider -height 20 {[cli] mac tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] mac tx fcs}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/crc32_inst/*}
    add wave -noupdate -divider -height 20 {[cli] mac mac interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/mac/*}
    add wave -noupdate -divider -height 20 {[cli] mac tx mux}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/eth_vlg_tx_mux_inst/*}
}

if {$SHOW_IP_CLI == 1} {
    add wave -noupdate -divider -height 20 {[cli] ipv4 top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {[cli] ipv4 rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] ipv4 rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {[cli] ipv4 tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] ipv4 tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {[cli] ipv4 mac tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/mac/*}
    add wave -noupdate -divider -height 20 {[cli] ipv4 tx mux}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/eth_vlg_tx_mux_isnt/*}
    add wave -noupdate -divider -height 20 {[cli] ipv4 arp table interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/arp_tbl/*}
}

if {$SHOW_ICMP_CLI == 1} {
    add wave -noupdate -divider -height 20 {=== [cli] ICMP ===}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/icmp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {[cli] ICMP rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/icmp_vlg_inst/icmp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] ICMP tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/icmp_vlg_inst/icmp_vlg_tx_inst/*}
}

if {$SHOW_TCP_CLI == 1} {
    add wave -noupdate -divider -height 20 {=== [cli] TCP rx ===}
    add wave -noupdate -divider -height 20 {[cli] TCP tx ipv4 interface in}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_rx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {[cli] TCP rx tcp interface out}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_rx_inst/tcp/*}
    add wave -noupdate -divider -height 20 {[cli] TCP rx logic}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_rx_inst/*}

    add wave -noupdate -divider -height 20 {=== [cli] TCP tx ===}
    add wave -noupdate -divider -height 20 {[cli] TCP tx ipv4 interface out}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_tx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {[cli] TCP tx tcp interface in}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_tx_inst/tcp/*}
    add wave -noupdate -divider -height 20 {[cli] TCP tx logic}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_tx_inst/*}
    
    add wave -noupdate -divider -height 20 {=== [cli] TCP Engine ===}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_engine_inst/*}
    add wave -noupdate -divider -height 20 {[cli] TCP Engine tcp tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_engine_inst/tx/*}
    add wave -noupdate -divider -height 20 {[cli] TCP Engine tcp rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_engine_inst/rx/*}
    add wave -noupdate -divider -height 20 {[cli] TCP Engine control interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_engine_inst/ctl/*}
    add wave -noupdate -divider -height 20 {[cli] TCP Keep-Alive}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_engine_inst/tcp_vlg_ka_inst/*}
    add wave -noupdate -divider -height 20 {[cli] TCP Fast Ack}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_engine_inst/tcp_vlg_fast_rtx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] TCP tx arbiter}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_engine_inst/tcp_vlg_tx_arb_inst/*}  

    add wave -noupdate -divider -height 20 {=== [cli] TCP tx control ===}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_tx_ctl_inst/*}
    add wave -noupdate -divider -height 20 {[cli] TCP tx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_tx_ctl_inst/ctl/*}
    add wave -noupdate -divider -height 20 {[cli] TCP tx control buffer}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_tx_ctl_inst/tcp_vlg_tx_buf_inst/*}
    add wave -noupdate -divider -height 20 {[cli] TCP tx control user interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_tx_ctl_inst/data/*}
    add wave -noupdate -divider -height 20 {[cli] TCP tx control interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_tx_ctl_inst/ctl/*}

    add wave -noupdate -divider -height 20 {=== [cli] TCP rx control ===}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_rx_ctl_inst/*}
    add wave -noupdate -divider -height 20 {[cli] TCP rx control user interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_rx_ctl_inst/ctl/*}
    add wave -noupdate -divider -height 20 {[cli] TCP rx control user interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_rx_ctl_inst/data/*}
    add wave -noupdate -divider -height 20 {[cli] TCP rx ack control}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_rx_ctl_inst/tcp_vlg_ack_inst/*}
    add wave -noupdate -divider -height 20 {[cli] TCP rx SACK}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_rx_ctl_inst/tcp_vlg_sack_inst/*}
    add wave -noupdate -divider -height 20 {[cli] TCP rx ack control rx interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/tcp_vlg_inst/tcp_vlg_core_inst/tcp_vlg_rx_ctl_inst/tcp_vlg_ack_inst/rx/*}
}

if {$SHOW_DHCP_CLI == 1} {
    add wave -noupdate -divider -height 20 {[cli] DHCP top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/dhcp_rx/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/dhcp_tx/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP UDP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/rx/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/dhcp_rx/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP UDP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/tx/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP DHCP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/dhcp_tx/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP core}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_core_inst/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] DHCP tx udp interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_tx_inst/udp/*}
}
if {$SHOW_UDP_CLI == 1} {
    add wave -noupdate -divider -height 20 {[cli] UDP}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/udp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {[cli] UDP RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] UDP ipv4 interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {[cli] UDP UDP interface rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/udp/*}
    add wave -noupdate -divider -height 20 {[cli] UDP TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/*}
    add wave -noupdate -divider -height 20 {[cli] UDP ipv4 interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/ipv4/*}
    add wave -noupdate -divider -height 20 {[cli] UDP UDP interface tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ipv4_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/udp/*}
}

if {$SHOW_ARP_CLI == 1} {
    add wave -noupdate -divider -height 20 {cli arp}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {cli arp rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {cli arp tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_vlg_tx_inst/*} 
    add wave -noupdate -divider -height 20 {cli arp tx mac interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_vlg_tx_inst/mac/*} 
    add wave -noupdate -divider -height 20 {cli arp table}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_table_inst/*} 
    add wave -noupdate -divider -height 20 {cli arp table interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/arp_vlg_inst/arp_table_inst/tbl/*} 
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
