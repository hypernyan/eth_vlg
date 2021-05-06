set FamilyDev "Cyclone 10 LP"
set PartDev "10CL025YU256I7G"
set MemDev "EPCQ64"
set FlashLoadDev "10CL025Y"

set PrjRef "c10lp_eval_kit"

lappend SrcDir "../src/ip"
lappend SrcDir "../src"
lappend SrcDir "../../esg_include"
lappend SrcDir "../../esg_hdl/src"
lappend SrcDir "../../../hdl_generics/src"
lappend SrcDir "../../../src"
lappend SrcDir "../../../vendors"

source "../../scripts/compile_intel.tcl"

