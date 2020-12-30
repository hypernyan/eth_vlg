set library_file_list {
	design_library {

	}
	test_library {
    ../src/eth_vlg_pkgs.sv
    ../../hdl_generics/src/fifo.sv
    ../../hdl_generics/src/mem_arb.sv
    ../../hdl_generics/src/ram.sv
    ../../hdl_generics/src/buf_mng.sv
    ../../hdl_generics/src/onehot.sv
    ../../hdl_generics/src/crc32.sv
    ../../hdl_generics/src/prng.sv
    ../../hdl_generics/src/sum.sv
    
    ../src/arp_vlg.sv
    ../src/mac_vlg.sv
    ../src/ipv4_vlg.sv
    ../src/icmp_vlg.sv
    ../src/udp_vlg.sv
    ../src/tcp_vlg.sv
    ../src/dhcp_vlg.sv
    ../src/eth_vlg.sv
    ../src/eth_vlg_tx_mux.sv
    
    sim/base_class_sim.sv
    sim/arp_vlg_sim.sv
    sim/ipv4_vlg_sim.sv
    sim/icmp_vlg_sim.sv
    sim/tcp_vlg_sim.sv
    sim/udp_vlg_sim.sv
    sim/dhcp_vlg_sim.sv
    sim/gateway_sim.sv
    sim/device_sim.sv
    sim/switch_sim.sv 
    sim/hexdump.sv
    sim/tb.sv
	}
}

set dut_wave_do wave_config.do

set top_level test_library.tb

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
eval vsim -novopt  $top_level
do $dut_wave_do
run 300000
if [llength $wave_patterns] {
  if $tk_ok {wave zoom range 7900ns 8900ns}
}


