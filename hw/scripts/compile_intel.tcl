proc findFiles { basedir pattern } {
    set fileList {}
    set x {}
    foreach x $basedir {
        set x [string trimright [file join [file normalize $x] { }]]
    
        foreach fileName [glob -nocomplain -type {f r} -path $x $pattern] {
            lappend fileList $fileName
        }	
    
        foreach dirName [glob -nocomplain -type {d  r} -path $x *] {
            set subDirList [findFiles $dirName $pattern]
            if { [llength $subDirList] > 0 } {
                foreach subDirFile $subDirList {
	    			lappend fileList $subDirFile
                }
            }
        }
    }
    return $fileList
}

proc relTo {targetfile currentpath} {
  set cc [file split [file normalize $currentpath]]
  set tt [file split [file normalize $targetfile]]
  if {![string equal [lindex $cc 0] [lindex $tt 0]]} {
      # not on *n*x then
      return -code error "$targetfile not on same volume as $currentpath"
  }
  while {[string equal [lindex $cc 0] [lindex $tt 0]] && [llength $cc] > 0} {
      # discard matching components from the front
      set cc [lreplace $cc 0 0]
      set tt [lreplace $tt 0 0]
  }
  set prefix ""
  if {[llength $cc] == 0} {
      # just the file name, so targetfile is lower down (or in same place)
      set prefix "."
  }
  # step up the tree
  for {set i 0} {$i < [llength $cc]} {incr i} {
      append prefix " .."
  }
  # stick it all together (the eval is to flatten the targetfile list)
  return [eval file join $prefix $tt]
}

# "pwd"
set TclPath [file dirname [file normalize [info script]]]

# Example projects are in PrjPool
set PrjPool [string range $TclPath 0 [string last / $TclPath]]

# Project location
set PrjDir $PrjPool/$PrjRef

set PrjName $PrjRef.qpf

set QuartusNm "quartus"
set QuartusDir $PrjPool/$PrjRef/$QuartusNm

cd $PrjDir

if {[file exists $QuartusNm] == 1} { file delete -force $QuartusNm }
file mkdir $QuartusNm
cd $QuartusDir

set SrcVHD   [findFiles $SrcDir "*.vhd"]
set SrcV     [findFiles $SrcDir "*.v"  ]
set SrcSV    [findFiles $SrcDir "*.sv" ]
set SrcQIP   [findFiles $SrcDir "*.qip"]
set SrcMIF   [findFiles $SrcDir "*.mif"]
set SrcSDC   [findFiles $SrcDir "*.sdc"]

set SrcVHD_rel {}
set SrcV_rel   {}
set SrcSV_rel  {}
set SrcQIP_rel {}
set SrcMIF_rel {}
set SrcSDC_rel {}

set x {}

foreach x $SrcVHD {
	set x [relTo $x $QuartusDir]
	lappend SrcVHD_rel $x
}

foreach x $SrcV {
	set x [relTo $x $QuartusDir]
	lappend SrcV_rel $x
}

foreach x $SrcSV {
	set x [relTo $x $QuartusDir]
	lappend SrcSV_rel $x
}

foreach x $SrcQIP {
	set x [relTo $x $QuartusDir]
	lappend SrcQIP_rel $x
}

foreach x $SrcMIF {
	set x [relTo $x $QuartusDir]
	lappend SrcMIF_rel $x
}

foreach x $SrcSDC {
	set x [relTo $x $QuartusDir]
	lappend SrcSDC_rel $x
}

project_new $PrjRef -family $FamilyDev -part $PartDev -overwrite
project_open $PrjRef

set CurrentFile {}

foreach CurrentFile $SrcVHD_rel {
	set_global_assignment -name VHDL_FILE $CurrentFile
	puts "Adding VHDL file: $CurrentFile"
}	
foreach CurrentFile $SrcV_rel {
	set_global_assignment -name VERILOG_FILE $CurrentFile
	puts "Adding Verilog file: $CurrentFile"
}	
foreach CurrentFile $SrcSV_rel {
	set_global_assignment -name SYSTEMVERILOG_FILE $CurrentFile
	puts "Adding SystemVerilog file: $CurrentFile"
}	
foreach CurrentFile $SrcQIP_rel {
	set_global_assignment -name QIP_FILE $CurrentFile
	puts "Adding QIP file: $CurrentFile"
}	
foreach CurrentFile $SrcMIF_rel {
	set_global_assignment -name MIF_FILE $CurrentFile
	puts "Adding MIF file: $CurrentFile"
}
foreach CurrentFile $SrcSDC_rel {
	set_global_assignment -name SDC_FILE $CurrentFile
	puts "Adding SDC file: $CurrentFile"
}

# Set optimization mode
set_global_assignment -name OPTIMIZATION_MODE "HIGH PERFORMANCE EFFORT"

cd $QuartusDir
load_package flow

# QSF settings
set AssigPath "/tcl/assignments.tcl"
source $PrjPool/$PrjRef/$AssigPath
set_global_assignment -name TOP_LEVEL_ENTITY top


execute_module -tool map
execute_module -tool fit
execute_module -tool asm
execute_module -tool sta
cd $TclPath
source "jic.tcl"
