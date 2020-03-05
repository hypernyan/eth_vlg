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
set TclPath [file dirname [file normalize [info script]]]
set NewLoc [string range $TclPath 0 [string last / $TclPath]-5]

set FamilyDev "Cyclone V"
set PartDev "5CEBA5F23C8"
set MemDev "EPCS64"
set FlashLoadDev "5CEBA5"

set PrjDir  [string range $TclPath 0 [string last / $NewLoc]-1]
puts "Project location is: $PrjDir"

set TopName [string range $NewLoc    [string last / $NewLoc]+1 end]

set PrjName $TopName.qpf
set TopDir $PrjDir/$TopName
set SrcDir $PrjDir/$TopName/src
set QuartusNm "quartus"
set QuartusDir $PrjDir/$TopName/$QuartusNm
set DDR_pin_assignments [findFiles $SrcDir "*_pin_assignments.tcl"]



cd $PrjDir/$TopName
pwd

cd $QuartusDir
load_package flow

project_open $TopName

puts $quartus(nameofexecutable);

if {$DDR_pin_assignments ne ""} {
	puts "Running DDR pin assignment script: $DDR_pin_assignments"
	source $DDR_pin_assignments
} else { 
	puts "No DDR pin assignment script found"
}
