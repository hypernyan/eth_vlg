set SHOW_TOP  0
set SHOW_MAC_CLI  1
set SHOW_MAC_SRV  1
set SHOW_ARP      0
set SHOW_IP_CLI   0
set SHOW_IP_SRV   0
set SHOW_ICMP_CLI 0
set SHOW_ICMP_SRV 0
set SHOW_TCP_CLI  0
set SHOW_TCP_SRV  0
set SHOW_TCP_TX_QUEUE_CLI 0
set SHOW_TCP_TX_QUEUE_SRV 0
set SHOW_TCP_RX_CLI 0
set SHOW_TCP_RX_SRV 0
set SHOW_TCP_TX_CLI 0
set SHOW_TCP_TX_SRV 0
onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider -height 40 {TESTBENCH}
add wave -noupdate -format Logic -radix hexadecimal {tb/*}
add wave -noupdate -format Logic -radix hexadecimal {tb/phy_cli2srv/d}
add wave -noupdate -format Logic -radix hexadecimal {tb/phy_cli2srv/v}
add wave -noupdate -format Logic -radix hexadecimal {tb/phy_srv2cli/d}
add wave -noupdate -format Logic -radix hexadecimal {tb/phy_srv2cli/v}

#===============================================
if {$SHOW_MAC_CLI == 1} {
    add wave -noupdate -divider -height 20 {MAC}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/d}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/sof}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/eof}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/hdr}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/d}
}
if {$SHOW_MAC_SRV == 1} {
    add wave -noupdate -divider -height 20 {MAC}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/d}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/sof}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/eof}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/hdr}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/d}
}
#===============================================
if {$SHOW_IP_CLI == 1} {
    add wave -noupdate -divider -height 20 {IP Client}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {IP Client RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {IP Client TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
}
if {$SHOW_IP_SRV == 1} {
    add wave -noupdate -divider -height 20 {IP Server}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {IP Server RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {IP Server TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
}
#===============================================
if {$SHOW_ICMP_CLI == 1} {
    add wave -noupdate -divider -height 20 {ICMP Client}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_tx_inst/*}
}
if {$SHOW_ICMP_SRV == 1} {

    add wave -noupdate -divider -height 20 {ICMP Server}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_tx_inst/*}
}
#===============================================
if {$SHOW_TCP_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP Client}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/*}
}
if {$SHOW_TCP_SRV == 1} {
    add wave -noupdate -divider -height 20 {TCP Server}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/*}
}
if {$SHOW_TCP_TX_QUEUE_CLI == 1} {
    add wave -noupdate -divider -height 20 {Client Queue}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_tx_queue_inst/*}
    add wave -noupdate -divider -height 20 {Queue RAM}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_tx_queue_inst/tcp_data_queue_inst/*}
}
if {$SHOW_TCP_TX_QUEUE_SRV == 1} {
    add wave -noupdate -divider -height 20 {Server Queue}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_tx_queue_inst/*}
    add wave -noupdate -divider -height 20 {Queue RAM}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_tx_queue_inst/tcp_data_queue_inst/*}
}
if {$SHOW_TCP_RX_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP Rx Cli}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_vlg_rx_inst/*}
}
if {$SHOW_TCP_RX_SRV == 1} {
    add wave -noupdate -divider -height 20 {TCP Rx Srv}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_vlg_rx_inst/*}
}
if {$SHOW_TCP_TX_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP Tx Cli}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_vlg_tx_inst/*}
}
if {$SHOW_TCP_TX_SRV == 1} {
    add wave -noupdate -divider -height 20 {TCP Tx Srv}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_vlg_tx_inst/*}
}

#===============================================
#if {$SHOW_ARP == 1} {
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
#}

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
