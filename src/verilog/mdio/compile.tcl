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
			mdio_master.sv
			mdio_tb.sv
			nf2_mdio.sv
		}
}
set top_level              test_library.mdio_tb
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
if [llength $wave_patterns] {
  noview wave
  foreach pattern $wave_patterns {
    add wave $pattern
  }
  configure wave -signalnamewidth 1
  foreach {radix signals} $wave_radices {
    foreach signal $signals {
      catch {property wave -radix $radix $signal}
    }
  }
  if $tk_ok {wm geometry $waveTopLevel [winfo screenwidth .]x[winfo screenheight .]+0+0}
}

# Run the simulation
run 30000000

# If waves are required

if [llength $wave_patterns] {
  if $tk_ok {wave zoom full}
}

puts {
  Script commands are:

  r = Recompile changed and dependent files
 rr = Recompile everything
  q = Quit without confirmation
}


