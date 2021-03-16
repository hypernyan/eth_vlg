

set file [ open "$TclPath/jic.cof" "w" ]
puts $file {<?xml version="1.0" encoding="US-ASCII" standalone="yes"?>}
puts $file <cof>
puts $file <eprom_name>$MemDev</eprom_name>
puts $file <flash_loader_device>$FlashLoadDev</flash_loader_device>
puts $file <output_filename>$TclPath/out.jic</output_filename>
puts $file <n_pages>1</n_pages>
puts $file <width>1</width>
puts $file <mode>7</mode>
puts $file <sof_data>
puts $file <user_name>Page_0</user_name>
puts $file <page_flags>1</page_flags>
puts $file <bit0>
puts $file <sof_filename>$QuartusDir/$PrjRef.sof<compress_bitstream>1</compress_bitstream></sof_filename>
puts $file </bit0>
puts $file </sof_data>
puts $file <version>10</version>
puts $file <create_cvp_file>0</create_cvp_file>
puts $file <create_hps_iocsr>0</create_hps_iocsr>
puts $file <auto_create_rpd>0</auto_create_rpd>
puts $file <rpd_little_endian>1</rpd_little_endian>
puts $file <options>
puts $file <map_file>1</map_file>
puts $file </options>
puts $file <advanced_options>
puts $file <ignore_epcs_id_check>2</ignore_epcs_id_check>
puts $file <ignore_condone_check>2</ignore_condone_check>
puts $file <plc_adjustment>0</plc_adjustment>
puts $file <post_chain_bitstream_pad_bytes>-1</post_chain_bitstream_pad_bytes>
puts $file <post_device_bitstream_pad_bytes>-1</post_device_bitstream_pad_bytes>
puts $file <bitslice_pre_padding>1</bitslice_pre_padding>
puts $file </advanced_options>
puts $file </cof>
close $file
puts "Generating .jic file..."
qexec "quartus_cpf -c $TclPath/jic.cof"
puts "Generating .jic file successfull"