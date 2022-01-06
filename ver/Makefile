#
CC = g++
CXXFLAGS = -std=c++17 -Wall -g
.PHONY: all
all: run

VERILATOR       = verilator
SRC             = ../src/
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e "s/^.*=\s*//"')
VINC           := $(VERILATOR_ROOT)/include
TOP             = top
PARAMS_SVH      = params.svh
PARAMS_HPP      = params.h
# packages
RTLSRC += $(SRC)eth_vlg_pkg.sv
RTLSRC += $(SRC)mac/mac_vlg_pkg.sv
RTLSRC += $(SRC)arp/arp_vlg_pkg.sv
RTLSRC += $(SRC)ipv4/ipv4_vlg_pkg.sv
RTLSRC += $(SRC)icmp/icmp_vlg_pkg.sv
RTLSRC += $(SRC)tcp/tcp_vlg_pkg.sv
RTLSRC += $(SRC)udp/udp_vlg_pkg.sv
RTLSRC += $(SRC)dhcp/dhcp_vlg_pkg.sv
# interfaces
RTLSRC += $(SRC)phy_ifc.sv
RTLSRC += $(SRC)mac/mac_ifc.sv
RTLSRC += $(SRC)arp/arp_data_ifc.sv
RTLSRC += $(SRC)arp/arp_tbl_ifc.sv
RTLSRC += $(SRC)dhcp/dhcp_ctl_ifc.sv
RTLSRC += $(SRC)dhcp/dhcp_ifc.sv
RTLSRC += $(SRC)icmp/icmp_ifc.sv
RTLSRC += $(SRC)ipv4/ipv4_ifc.sv
RTLSRC += $(SRC)tcp/tcp_ifc.sv
RTLSRC += $(SRC)tcp/tcp_ctl_ifc.sv
RTLSRC += $(SRC)tcp/tcp_data_ifc.sv
RTLSRC += $(SRC)tcp/tcp_rx_ctl_ifc.sv
RTLSRC += $(SRC)tcp/tcp_tx_ctl_ifc.sv
RTLSRC += $(SRC)udp/udp_ctl_ifc.sv
RTLSRC += $(SRC)udp/udp_data_ifc.sv
RTLSRC += $(SRC)udp/udp_ifc.sv
# util
RTLSRC += $(SRC)util/eth_vlg_crc32.sv
RTLSRC += $(SRC)util/eth_vlg_sum.sv
RTLSRC += $(SRC)util/eth_vlg_onehot.sv
RTLSRC += $(SRC)util/eth_vlg_ram_sp.sv
RTLSRC += $(SRC)util/eth_vlg_ram_dp.sv
RTLSRC += $(SRC)util/ram_dp_ifc.sv
RTLSRC += $(SRC)util/fifo_sc_ifc.sv
RTLSRC += $(SRC)util/fifo_dc_ifc.sv
RTLSRC += $(SRC)util/eth_vlg_fifo_sc.sv
RTLSRC += $(SRC)util/eth_vlg_fifo_dc.sv
RTLSRC += $(SRC)util/ram_sp_ifc.sv
RTLSRC += $(SRC)util/prng.sv
RTLSRC += $(SRC)util/eth_vlg_tmr.sv
RTLSRC += $(SRC)util/eth_vlg_tx_mux.sv
# arp
RTLSRC += $(SRC)arp/arp_vlg_rx.sv
RTLSRC += $(SRC)arp/arp_vlg_table.sv
RTLSRC += $(SRC)arp/arp_vlg_tx.sv
RTLSRC += $(SRC)arp/arp_vlg.sv
# dhcp
RTLSRC += $(SRC)dhcp/dhcp_vlg_core.sv
RTLSRC += $(SRC)dhcp/dhcp_vlg_rx.sv
RTLSRC += $(SRC)dhcp/dhcp_vlg_tx.sv
RTLSRC += $(SRC)dhcp/dhcp_vlg.sv
# icmp
RTLSRC += $(SRC)icmp/icmp_vlg_rx.sv
RTLSRC += $(SRC)icmp/icmp_vlg_tx.sv
RTLSRC += $(SRC)icmp/icmp_vlg.sv
# ipv4
RTLSRC += $(SRC)ipv4/ipv4_vlg_rx.sv
RTLSRC += $(SRC)ipv4/ipv4_vlg_top.sv
RTLSRC += $(SRC)ipv4/ipv4_vlg_tx.sv
RTLSRC += $(SRC)ipv4/ipv4_vlg.sv
# mac
RTLSRC += $(SRC)mac/mac_vlg_cdc.sv
RTLSRC += $(SRC)mac/mac_vlg_rx.sv
RTLSRC += $(SRC)mac/mac_vlg_tx.sv
RTLSRC += $(SRC)mac/mac_vlg.sv
# tcp
RTLSRC += $(SRC)tcp/tcp_vlg_core.sv
RTLSRC += $(SRC)tcp/tcp_vlg_fast_rtx.sv
RTLSRC += $(SRC)tcp/tcp_vlg_rx.sv
RTLSRC += $(SRC)tcp/tcp_vlg_seq.sv
RTLSRC += $(SRC)tcp/tcp_vlg_tx_add.sv
RTLSRC += $(SRC)tcp/tcp_vlg_tx_buf.sv
RTLSRC += $(SRC)tcp/tcp_vlg_tx_info.sv
RTLSRC += $(SRC)tcp/tcp_vlg_tx_strm.sv
RTLSRC += $(SRC)tcp/tcp_vlg_ack.sv
RTLSRC += $(SRC)tcp/tcp_vlg_engine.sv
RTLSRC += $(SRC)tcp/tcp_vlg_ka.sv
RTLSRC += $(SRC)tcp/tcp_vlg_rx_ctl.sv
RTLSRC += $(SRC)tcp/tcp_vlg_sack.sv
RTLSRC += $(SRC)tcp/tcp_vlg.sv
RTLSRC += $(SRC)tcp/tcp_vlg_tx_arb.sv
RTLSRC += $(SRC)tcp/tcp_vlg_tx_ctl.sv
RTLSRC += $(SRC)tcp/tcp_vlg_tx_scan.sv
RTLSRC += $(SRC)tcp/tcp_vlg_tx.sv
# udp
RTLSRC += $(SRC)udp/udp_vlg_rx.sv
RTLSRC += $(SRC)udp/udp_vlg_top.sv
RTLSRC += $(SRC)udp/udp_vlg_tx_ctl.sv
RTLSRC += $(SRC)udp/udp_vlg_tx.sv
RTLSRC += $(SRC)udp/udp_vlg.sv

RTLSRC += $(SRC)eth_vlg.sv
RTLSRC += switch_sim.sv
RTLSRC += top.sv

# Testbench headers
 TBHDRSRC  = hdr/dev_c.h
 TBHDRSRC += hdr/icmp_c.h
 TBHDRSRC += hdr/udp_c.h
 TBHDRSRC += hdr/arp_c.h
 TBHDRSRC += hdr/dhcp_c.h
 TBHDRSRC += hdr/ipv4_c.h
 TBHDRSRC += hdr/mac_c.h
 TBHDRSRC += hdr/pcap.h
 TBHDRSRC += hdr/pkt.h
 TBHDRSRC += hdr/usr.h
 #TBHDRSRC += adapter.h

# Testbench headers
 TBCPPSRC  = cpp/dev_c.cpp
 TBCPPSRC += cpp/icmp_c.cpp
 TBCPPSRC += cpp/udp_c.cpp
 TBCPPSRC += cpp/arp_c.cpp
 TBCPPSRC += cpp/dhcp_c.cpp
 TBCPPSRC += cpp/ipv4_c.cpp
 TBCPPSRC += cpp/mac_c.cpp
 TBCPPSRC += cpp/pcap.cpp
 TBCPPSRC += cpp/pkt.cpp
 TBCPPSRC += cpp/usr.cpp
# TBCPPSRC += adapter.cpp

# Flags
VERILATOR_FLAGS = -debug
# Allow different width arithmetic
VERILATOR_FLAGS += -Wno-WIDTH
# Similar words
VERILATOR_FLAGS += -Wno-SYMRSVDWORD
# Enable waveform dump
VERILATOR_FLAGS += --trace
# C++ output
VERILATOR_FLAGS += -cc

# verilated model
obj_dir/V$(TOP).cpp: $(RTLSRC)
	$(VERILATOR) $(VERILATOR_FLAGS) $(RTLSRC) --top-module $(TOP)

obj_dir/V$(TOP)__ALL.a: obj_dir/V$(TOP).cpp
	make --no-print-directory -C obj_dir -f V$(TOP).mk

# create executable 

top_tb: $(TOP).cpp obj_dir/V$(TOP)__ALL.a 
	$(CC) $(CXXFLAGS) -I$(VINC) -I obj_dir $(VINC)/verilated.cpp		\
		$(VINC)/verilated_vcd_c.cpp $(TBCPPSRC) $(TBCPPHDR) $(TOP).cpp -pthread $(VWRAP)	\
		obj_dir/V$(TOP)__ALL.a -o $(TOP)_tb

.PHONY: run
run: top_tb
	./top_tb

.PHONY: clean
clean:
	rm -rf obj_dir/ eth_vlg/ top_tb eth_vlg.vcd
