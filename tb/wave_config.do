set SHOW_TOP  1
set SHOW_MAC_CLI  0
set SHOW_MAC_SRV  0
set SHOW_ARP_CLI  0
set SHOW_ARP_SRV  0
set SHOW_IP_CLI   0
set SHOW_IP_SRV   0
set SHOW_ICMP_CLI 0
set SHOW_ICMP_SRV 0
set SHOW_TCP_CLI  1
set SHOW_TCP_SRV  1
set SHOW_TCP_TX_QUEUE_CLI 0
set SHOW_TCP_TX_QUEUE_SRV 1
set SHOW_TCP_TX_CLI 0
set SHOW_TCP_TX_SRV 0
onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider -height 40 {TESTBENCH}
add wave -noupdate -format Logic -radix hexadecimal {tb/*}

#===============================================
if {$SHOW_MAC_CLI == 1} {
    add wave -noupdate -divider -height 20 {MAC}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_d}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_sof}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_eof}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_hdr}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy_v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy_d}
}
if {$SHOW_MAC_SRV == 1} {
    add wave -noupdate -divider -height 20 {MAC}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_d}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_sof}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_eof}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac_hdr}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy_v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy_d}
}
#===============================================
if {$SHOW_IP_CLI == 1} {
    add wave -noupdate -divider -height 20 {IP Client}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
}
if {$SHOW_IP_SRV == 1} {
    add wave -noupdate -divider -height 20 {IP Server}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
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
    add wave -noupdate -divider -height 20 {TCP}
    add wave -noupdate -divider -height 20 {Client}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/tcb}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/tcb_created}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/connected}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/connect}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/tcp_fsm}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_seq}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_data}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_addr}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_val}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_len}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_cs}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/ack_timer}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rem_port}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rem_ipv4}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rx_tcp_hdr}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rx_tcp_hdr_v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rx_d}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rx_v}

}
if {$SHOW_TCP_SRV == 1} {
    add wave -noupdate -divider -height 20 {Server}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/tcb}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/tcb_created}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/connected}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/tcp_fsm}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_seq}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_data}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_addr}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_val}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_len}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/queue_cs}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/ack_timer}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rem_port}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rem_ipv4}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rx_tcp_hdr}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rx_tcp_hdr_v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rx_d}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_server_inst/rx_v}
}
if {$SHOW_TCP_TX_QUEUE_CLI == 1} {
    add wave -noupdate -divider -height 20 {Queue Cli}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_tx_queue_inst/*}
}
if {$SHOW_TCP_TX_QUEUE_SRV == 1} {
    add wave -noupdate -divider -height 20 {Queue Srv}
    add wave -noupdate -format Logic -radix hexadecimal {tb/srv_inst/ip_vlg_top_inst/tcp_vlg_inst/tcp_tx_queue_inst/*}
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
WaveRestoreZoom {0 ps} {20 us}
