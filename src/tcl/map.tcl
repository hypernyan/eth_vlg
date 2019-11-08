
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

cd $PrjDir/$TopName
pwd

cd $QuartusDir
load_package flow

project_open $TopName

puts $quartus(nameofexecutable);

execute_module -tool map

project_close

