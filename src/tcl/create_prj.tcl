proc findFiles { basedir pattern } {

    set basedir [string trimright [file join [file normalize $basedir] { }]]
    set fileList {}
	
    foreach fileName [glob -nocomplain -type {f r} -path $basedir $pattern] {
        lappend fileList $fileName
    }	
	
    foreach dirName [glob -nocomplain -type {d  r} -path $basedir *] {
        set subDirList [findFiles $dirName $pattern]
        if { [llength $subDirList] > 0 } {
            foreach subDirFile $subDirList {
		lappend fileList $subDirFile
            }
        }
    }
    return $fileList
}

proc srcfilesafe {filename args} {
     global argv

     set save $argv
     set argv $args
     set rc [catch {source $filename} ret]
     set argv $save
     return -code $rc $ret
}

set TclPath [file dirname [file normalize [info script]]]
set NewLoc [string range $TclPath 0 [string last / $TclPath]-5]

set FamilyDev "Cyclone V"
set PartDev "5CEBA5F23C8"
set MemDev "EPCS64"
set FlashLoadDev "5CEBA5"

set PrjDir  [string range $TclPath 0 [string last / $NewLoc]-1]
puts "Project location is: $PrjDir"

set TopName eth_top

set PrjName $TopName.qpf
set TopDir $PrjDir/eth_vlg
set SrcDir $PrjDir/eth_vlg/src
set QuartusNm "quartus"
set QuartusDir $PrjDir/eth_vlg/$QuartusNm

cd $PrjDir/eth_vlg
pwd

if {[file exists $QuartusNm] == 1} { file delete -force $QuartusNm }
file mkdir $QuartusNm
cd $QuartusDir

set SrcVHD [findFiles $SrcDir "*.vhd"]
set SrcV   [findFiles $SrcDir "*.v"  ]
set SrcSV  [findFiles $SrcDir "*.sv" ]
set SrcQIP [findFiles $SrcDir "*.qip"]
set SrcMIF [findFiles $SrcDir "*.mif"]
set SrcSDC [findFiles $SrcDir "*.sdc"]

project_new eth_vlg -family $FamilyDev -part $PartDev -overwrite
project_open eth_vlg

set CurrentFile { } 
foreach CurrentFile $SrcVHD {
	set_global_assignment -name VHDL_FILE $CurrentFile
	puts "Adding VHDL file: $CurrentFile"
}	
set CurrentFile { } 
foreach CurrentFile $SrcV {
	set_global_assignment -name VERILOG_FILE $CurrentFile
	puts "Adding Verilog file: $CurrentFile"
}	
set CurrentFile { } 
foreach CurrentFile $SrcSV {
	set_global_assignment -name SYSTEMVERILOG_FILE $CurrentFile
	puts "Adding SystemVerilog file: $CurrentFile"
}	
set CurrentFile { } 
foreach CurrentFile $SrcQIP {
	set_global_assignment -name QIP_FILE $CurrentFile
	puts "Adding QIP file: $CurrentFile"
}	
foreach CurrentFile $SrcMIF {
	set_global_assignment -name MIF_FILE $CurrentFile
	puts "Adding MIF file: $CurrentFile"
}
foreach CurrentFile $SrcSDC {
	set_global_assignment -name SDC_FILE $CurrentFile
	puts "Adding SDC file: $CurrentFile"
}

cd $QuartusDir
load_package flow
# QSF settings
set_global_assignment -name FMAX_REQUIREMENT 125MHz
set_global_assignment -name TIMEQUEST_MULTICORNER_ANALYSIS ON
set_global_assignment -name SMART_RECOMPILE ON
set_global_assignment -name NUM_PARALLEL_PROCESSORS 6

execute_module -tool map
execute_module -tool fit
execute_module -tool asm
execute_module -tool sta

source $TclPath/conv.tcl
