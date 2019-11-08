puts {
  ModelSimSE general compile script version 1.1
  Copyright (c) Doulos June 2004, SD
}

# Simply change the project settings in this section
# for each new project. There should be no need to
# modify the rest of the script.

set library_file_list {
		design_library {

		}
		test_library {
			../../src/verilog/components/sim/hexdump.sv
			../../src/verilog/components/buf_mng.sv
			../../src/verilog/components/eth_vlg_buf.sv
			../../src/verilog/components/fifo_dc.sv
			../../src/verilog/components/fifo_sc.sv
			../../src/verilog/components/onehot_lsb.sv
			../../src/verilog/components/onehot_msb.sv
			../../src/verilog/components/stretch.sv
			../../src/verilog/components/true_dpram_sclk.sv
			../../src/verilog/components/timer.sv

			../../src/verilog/mac/mac_vlg_pkg.sv
			../../src/verilog/ipv4/ip_vlg_pkg.sv
			../../src/verilog/arp/arp_vlg_pkg.sv
			../../src/verilog/icmp/icmp_vlg_pkg.sv
			../../src/verilog/udp/udp_vlg_pkg.sv
			../../src/verilog/tcp/tcp_vlg_pkg.sv
			../../src/verilog/top/eth_vlg_pkg.sv

			../../src/verilog/arp/arp_vlg.sv
			../../src/verilog/arp/arp_vlg_rx.sv
			../../src/verilog/arp/arp_vlg_tx.sv
			../../src/verilog/arp/arp_table.sv

			../../src/verilog/mac/crc32.sv
			../../src/verilog/mac/mac_vlg.sv
			../../src/verilog/mac/mac_vlg_rx.sv
			../../src/verilog/mac/mac_vlg_sync.sv
			../../src/verilog/mac/mac_vlg_tx.sv

			../../src/verilog/ipv4/ip_vlg_top.sv
			../../src/verilog/ipv4/ipv4_vlg.sv
			../../src/verilog/ipv4/ipv4_vlg_rx.sv
			../../src/verilog/ipv4/ipv4_vlg_frag_rx.sv
			../../src/verilog/ipv4/ipv4_frag_buf.sv
			../../src/verilog/ipv4/ipv4_vlg_tx.sv

			../../src/verilog/icmp/icmp_vlg.sv
			../../src/verilog/icmp/icmp_vlg_rx.sv
			../../src/verilog/icmp/icmp_vlg_tx.sv

			../../src/verilog/udp/udp_vlg.sv
			../../src/verilog/udp/udp_vlg_rx.sv
			../../src/verilog/udp/udp_vlg_tx.sv

			../../src/verilog/tcp/tcp_vlg_rx.sv
			../../src/verilog/tcp/tcp_vlg.sv
			../../src/verilog/tcp/tcp_server.sv

			../../src/verilog/top/eth_vlg.sv

			../pkt_gen/sim_eth_vlg_pkg.sv
			../pkt_gen/pkt_gen.sv

			tb.sv
		}
}

set dut_wave_do wave_config.do

set top_level test_library.tb

set wave_patterns {
	/*
}

set wave_radices {
	hexadecimal {current_5v current_12v}
}

set waveWinName [ view wave -undock ]
set waveTopLevel [winfo toplevel $waveWinName]
puts $library_file_list

puts " Wave window name is : $waveTopLevel" 

# After sourcing the script from ModelSim for the
# first time use these commands to recompile.

proc r  {} {uplevel #0 source compile.tcl}
proc rr {} {global last_compile_time
            set last_compile_time 0
            r                            }
proc q  {} {quit -force                  }

#Does this installation support Tk?
set tk_ok 1
if [catch {package require Tk}] {set tk_ok 0}

# Prefer a fixed point font for the transcript
set PrefMain(font) {Courier 10 roman normal}

# Compile out of date files
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

# Load the simulation
eval vsim -novopt  $top_level

# If waves are required
#if [llength $wave_patterns] {
#  noview wave
#  foreach pattern $wave_patterns {
#    add wave $pattern
#  }
#  configure wave -signalnamewidth 1
#  foreach {radix signals} $wave_radices {
#    foreach signal $signals {
#      catch {property wave -radix $radix $signal}
#    }
#  }
#  if $tk_ok {wm geometry $waveTopLevel [winfo screenwidth .]x[winfo screenheight .]+0+0}
#}

do $dut_wave_do

# Run the simulation
run 8000

# If waves are required

if [llength $wave_patterns] {
  if $tk_ok {wave zoom full}
}


