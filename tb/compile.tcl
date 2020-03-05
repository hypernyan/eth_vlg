set library_file_list {
		design_library {

		}
		test_library {
			../src/verilog/eth_vlg_pkgs.sv
			../src/verilog/components/sim/hexdump.sv
			../src/verilog/components/buf_mng.sv
			../src/verilog/components/eth_vlg_buf.sv
			../src/verilog/components/fifo.sv
			../src/verilog/components/onehot.sv
			../src/verilog/components/true_dpram_sclk.sv
			../src/verilog/components/crc32.sv
			../src/verilog/arp_vlg.sv
			../src/verilog/mac_vlg.sv
			../src/verilog/mac_vlg_sync.sv
			../src/verilog/ip_vlg_top.sv
			../src/verilog/ipv4_vlg.sv
			../src/verilog/icmp_vlg.sv
			../src/verilog/udp_vlg.sv
			../src/verilog/tcp/tcp_vlg_rx.sv
			../src/verilog/tcp/tcp_vlg_tx.sv
			../src/verilog/tcp/tcp_vlg_rx_queue.sv
			../src/verilog/tcp/tcp_vlg_tx_queue.sv
			../src/verilog/tcp/tcp_vlg_server.sv
			../src/verilog/tcp/tcp_vlg.sv
			../src/verilog/eth_vlg.sv
			tb.sv
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
run 30000
if [llength $wave_patterns] {
  if $tk_ok {wave zoom full}
}


