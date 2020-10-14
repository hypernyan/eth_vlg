set SHOW_TOP  0
set SHOW_MAC_CLI          1
set SHOW_MAC_SRV          0
set SHOW_ARP              0

set SHOW_IP_CLI           0
set SHOW_ICMP_CLI         0
set SHOW_TCP_CLI          0
set SHOW_TCP_ENGINE_CLI   0
set SHOW_TCP_TX_QUEUE_CLI 0
set SHOW_TCP_RX_CLI       0
set SHOW_TCP_TX_CLI       0
set SHOW_UDP_CLI          1
set SHOW_DHCP_CLI         1

set SHOW_IP_SRV           0
set SHOW_ICMP_SRV         0
set SHOW_TCP_SRV          0
set SHOW_TCP_ENGINE_SRV   0
set SHOW_TCP_TX_QUEUE_SRV 0
set SHOW_TCP_RX_SRV       0
set SHOW_TCP_TX_SRV       0
set SHOW_DHCP_SRV         1

onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider -height 40 {SIM DEVICE}
add wave -noupdate -format Logic -radix hexadecimal {tb/device_sim_inst/*}

add wave -noupdate -divider -height 40 {TESTBENCH}
add wave -noupdate -format Logic -radix hexadecimal {tb/clk}
add wave -noupdate -format Logic -radix hexadecimal {tb/rst}

add wave -noupdate -divider -height 20 {Server}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_din_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_vin_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_cts_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_snd_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_dout_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_vout_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/connect_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/connected_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/listen_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/rem_ipv4_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/rem_port_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/loc_port_srv}

add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_ipv4_req_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_pref_ipv4_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_ipv4_addr_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_ipv4_val_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_ok_srv}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_timeout_srv}

add wave -noupdate -divider -height 20 {Client}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_din_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_vin_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_cts_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_snd_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_dout_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/tcp_vout_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/connect_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/connected_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/listen_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/rem_ipv4_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/rem_port_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/loc_port_cli}

add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_ipv4_req_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_pref_ipv4_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_ipv4_addr_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_ipv4_val_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_ok_cli}
add wave -noupdate -format Logic -radix hexadecimal {tb/dhcp_timeout_cli}

add wave -noupdate -format Logic -radix hexadecimal {tb/phy_cli2srv/d}
add wave -noupdate -format Logic -radix hexadecimal {tb/phy_cli2srv/v}
add wave -noupdate -format Logic -radix hexadecimal {tb/phy_srv2cli/d}
add wave -noupdate -format Logic -radix hexadecimal {tb/phy_srv2cli/v}

add wave -noupdate -divider -height 20 { ////////////////// }
add wave -noupdate -divider -height 20 { ///// CLIENT ///// }
add wave -noupdate -divider -height 20 { ////////////////// }

#===============================================
if {$SHOW_MAC_CLI == 1} {
    add wave -noupdate -divider -height 20 {MAC}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -divider -height 20 {mac interface}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_rx_inst/mac/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/v}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/mac_vlg_inst/mac_vlg_tx_inst/phy/d}
}

if {$SHOW_IP_CLI == 1} {
    add wave -noupdate -divider -height 20 {IP Client}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {IP Client RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {IP Client TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
}

if {$SHOW_ICMP_CLI == 1} {
    add wave -noupdate -divider -height 20 {ICMP Client}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_tx_inst/*}
}

if {$SHOW_TCP_RX_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP RX Client}

    add wave -noupdate -divider -height 20 {IPv4 in}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_rx_inst/rx/*}

    add wave -noupdate -divider -height 20 {TCP out}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_rx_inst/tcp/*}
}

if {$SHOW_TCP_TX_CLI == 1} {
    add wave -noupdate -divider -height 20 {TCP TX Client}
    add wave -noupdate -divider -height 20 {IPv4 out}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/tx/*}
    add wave -noupdate -divider -height 20 {TCP in}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/tcp/*}
    add wave -noupdate -divider -height 20 {Logic}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/rst}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/fsm_rst}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/busy}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/transmitting}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/calc}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/hdr_done}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/calc_done}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/req}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/queue_data}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/queue_addr}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/cur_tcp_hdr}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/opt_assembled}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/shift_opt}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/gen_tcp[0]/tcp_vlg_inst/tcp_vlg_tx_inst/shift_opt}
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
    add wave -noupdate -divider -height 20 {rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/udp_vlg_inst/udp_vlg_tx_inst/*}
}
if {$SHOW_DHCP_CLI == 1} {
    add wave -noupdate -divider -height 20 {DHCP top}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/*}
    add wave -noupdate -divider -height 20 {DHCP rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_rx/*}
    add wave -noupdate -divider -height 20 {DHCP tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_tx/*}
    add wave -noupdate -divider -height 20 {UDP rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/rx/*}
    add wave -noupdate -divider -height 20 {UDP tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/tx/*}
    add wave -noupdate -divider -height 20 {core}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_core_inst/*}
    add wave -noupdate -divider -height 20 {rx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {tx}
    add wave -noupdate -format Logic -radix hexadecimal {tb/cli_inst/ip_vlg_top_inst/dhcp_vlg_inst/dhcp_vlg_tx_inst/*}
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
