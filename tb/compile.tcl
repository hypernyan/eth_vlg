set library_file_list {
	design_library {

	}
  test_library {
    ../hdl_generics/src/fifo.sv
    ../hdl_generics/src/mem_arb.sv
    ../hdl_generics/src/ram.sv
    ../hdl_generics/src/buf_mng.sv
    ../hdl_generics/src/onehot.sv
    ../hdl_generics/src/crc32.sv
    ../hdl_generics/src/prng.sv
    ../hdl_generics/src/sum.sv

    ../src/eth_vlg_pkg.sv
    ../src/arp/arp_vlg_pkg.sv
    ../src/mac/mac_vlg_pkg.sv
    ../src/ipv4/ipv4_vlg_pkg.sv
    ../src/icmp/icmp_vlg_pkg.sv
    ../src/udp/udp_vlg_pkg.sv
    ../src/tcp/tcp_vlg_pkg.sv

    ../src/eth_vlg_if.sv

    ../src/arp/arp_vlg_if.sv
    ../src/arp/arp_vlg.sv
    ../src/arp/arp_vlg_rx.sv
    ../src/arp/arp_vlg_tx.sv
    ../src/arp/arp_vlg_table.sv

    ../src/mac/mac_vlg_if.sv
    ../src/mac/mac_vlg_rx.sv
    ../src/mac/mac_vlg_tx.sv
    ../src/mac/mac_vlg.sv
    ../src/mac/mac_vlg_cdc.sv

    ../src/ipv4/ipv4_vlg_if.sv
    ../src/ipv4/ipv4_vlg_rx.sv
    ../src/ipv4/ipv4_vlg_tx.sv
    ../src/ipv4/ipv4_vlg.sv
    ../src/ipv4/ipv4_vlg_top.sv

    ../src/icmp/icmp_vlg_if.sv
    ../src/icmp/icmp_vlg_rx.sv
    ../src/icmp/icmp_vlg_tx.sv
    ../src/icmp/icmp_vlg.sv

    ../src/udp/udp_vlg_if.sv
    ../src/udp/udp_vlg_rx.sv
    ../src/udp/udp_vlg_tx.sv
    ../src/udp/udp_vlg.sv

    ../src/tcp/tcp_vlg_ack.sv
    ../src/tcp/tcp_vlg_core.sv
    ../src/tcp/tcp_vlg_engine.sv
    ../src/tcp/tcp_vlg_fast_rtx.sv
    ../src/tcp/tcp_vlg_if.sv
    ../src/tcp/tcp_vlg_ka.sv
    ../src/tcp/tcp_vlg_rx_ctl.sv
    ../src/tcp/tcp_vlg_rx.sv
    ../src/tcp/tcp_vlg_sack.sv
    ../src/tcp/tcp_vlg_tx_arb.sv
    ../src/tcp/tcp_vlg_tx_buf.sv
    ../src/tcp/tcp_vlg_tx_ctl.sv
    ../src/tcp/tcp_vlg_tx.sv
    ../src/tcp/tcp_vlg.sv

    ../src/dhcp/dhcp_vlg_pkg.sv
    ../src/dhcp/dhcp_vlg_if.sv
    ../src/dhcp/dhcp_vlg_rx.sv
    ../src/dhcp/dhcp_vlg_tx.sv
    ../src/dhcp/dhcp_vlg.sv
    ../src/dhcp/dhcp_vlg_core.sv

    ../src/util/eth_vlg_tmr.sv
    ../src/util/eth_vlg_tx_mux.sv

    ../src/eth_vlg_pkg.sv
    ../src/eth_vlg.sv

    ../sim/util/clkdef.sv
    ../sim/util/hexdump.sv
    ../sim/util/pcapdump.sv
    ../sim/util/rst_gen.sv
    ../sim/util/statistics.sv
    ../sim/util/switch_sim.sv 
    ../sim/util/sender.sv 
    ../sim/util/receiver.sv 

    ../sim/proto/base_vlg_sim.sv
    ../sim/proto/mac_vlg_sim.sv
    ../sim/proto/arp_vlg_sim.sv
    ../sim/proto/ipv4_vlg_sim.sv
    ../sim/proto/icmp_vlg_sim.sv
    ../sim/proto/tcp_vlg_sim.sv
    ../sim/proto/udp_vlg_sim.sv
    ../sim/proto/dhcp_vlg_sim.sv
    
    ../sim/gateway_sim.sv
    ../sim/device_sim.sv
    ../sim/user_logic.sv

    ../sim/sva/mac/mac_vlg_rx_sva.sv
    ../sim/sva/ipv4/ipv4_vlg_rx_sva.sv
    ../sim/sva/tcp/tcp_vlg_tx_ctl_sva.sv
    ../sim/sva/tcp/tcp_vlg_rx_ctl_sva.sv
    ../sim/sva/macros.sv 
    ../sim/sva/bindfiles.sv
    
    tb.sv
	}
}

set dut_wave_do wave_config.do

set top_level {test_library.tb test_library.bindfiles}


set wave_patterns {
	/*
}

set wave_radices {
	/*
}

set waveWinName [ view wave -undock ]
set waveTopLevel [winfo toplevel $waveWinName]
puts $library_file_list

proc r  {} {uplevel #0 source compile.tcl}
proc rr {} {global last_compile_time
            set last_compile_time 0
            r                            }
proc q  {} {quit -force                  }

set tk_ok 1
if [catch {package require Tk}] {set tk_ok 0}

set PrefMain(font) {Courier 10 roman normal}

set time_now [clock seconds]
if [catch {set last_compile_time}] {
  set last_compile_time 0
}
foreach {library file_list} $library_file_list {
  vlib $library
  vmap work $library
  foreach file $file_list {
    if { $last_compile_time < [file mtime $file] } {
      if [regexp {.vhdl?$} $file] {
        vcom -93 $file
      } else {
        vlog $file
      }
      set last_compile_time 0
    }
  }
}

set last_compile_time $time_now
eval vopt +acc $top_level -o tb_opt
eval vsim tb_opt
do $dut_wave_do
run 100000
if [llength $wave_patterns] {
  if $tk_ok {wave zoom range 810ns 910ns}
}
