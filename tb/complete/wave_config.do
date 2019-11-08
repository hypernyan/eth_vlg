set SHOW_TOP  1
set SHOW_MAC  1
set SHOW_ARP  1
set SHOW_IP   1
set SHOW_ICMP 1

onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider -height 40 {TESTBENCH}
add wave -noupdate -format Logic -radix hexadecimal {tb/*}
add wave -noupdate -format Logic -radix hexadecimal {tb/pkt_gen_inst/*}
#===============================================
if {$SHOW_MAC == 1} {
    add wave -noupdate -divider -height 20 {MAC}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/mac_vlg_inst/mac_vlg_rx_inst/*}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/mac_vlg_inst/mac_vlg_rx_inst/crc32_inst/*}

    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/mac_vlg_inst/mac_vlg_tx_inst/*}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/mac_vlg_inst/mac_vlg_tx_inst/*}
}
#===============================================
if {$SHOW_IP == 1} {
    add wave -noupdate -divider -height 20 {IP}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/ip_vlg_top_inst/*}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/ip_vlg_top_inst/ipv4_vlg_inst/ipv4_vlg_tx_inst/*}
}
#===============================================
if {$SHOW_ICMP == 1} {
    add wave -noupdate -divider -height 20 {ICMP}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/ip_vlg_top_inst/icmp_vlg_inst/icmp_vlg_tx_inst/*}
}
#===============================================
if {$SHOW_ARP == 1} {
    add wave -noupdate -divider -height 40 {ARP}
    add wave -noupdate -divider -height 20 {RX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/arp_vlg_inst/arp_vlg_rx_inst/*}
    add wave -noupdate -divider -height 20 {TX}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/arp_vlg_inst/arp_vlg_tx_inst/*} 
    add wave -noupdate -divider -height 40 {ARP Table}
    add wave -noupdate -format Logic -radix hexadecimal {tb/dut/arp_vlg_inst/arp_table_inst/*} 
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
