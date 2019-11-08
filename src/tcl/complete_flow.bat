call version.cmd
quartus_sh  -t create_prj.tcl
quartus_sh  -t map.tcl
quartus_sta -t ddr_pins.tcl
quartus_sh  -t fit.tcl
quartus_sh  -t asm.tcl
quartus_sh  -t sta.tcl
@echo off
set /p temp="Hit enter to exit"

