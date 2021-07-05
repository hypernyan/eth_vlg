
####################
# Reference clocks #
####################
create_clock -name clk_125m -period 8.0  -waveform {0 4}  [get_ports {gen_clk_125m}]
create_clock -name clk_100m -period 10.0 -waveform {0 5}  [get_ports {gen_clk_100m}]
create_clock -name clk_50m  -period 20.0 -waveform {0 10} [get_ports {gen_clk_50m}]

##############
# PLL clocks #
##############
create_generated_clock -source {rgmii_adapter_inst|rgmii_rx_pll_inst|altpll_component|auto_generated|pll1|inclk[0]} \
-duty_cycle 50.00 \
-name rgmii_rx_clk_pll \
{rgmii_adapter_inst|rgmii_rx_pll_inst|altpll_component|auto_generated|pll1|clk[0]} \
-phase 225

create_generated_clock -source {rgmii_adapter_inst|rgmii_tx_pll_inst|altpll_component|auto_generated|pll1|inclk[0]} \
-duty_cycle 50.00 \
-name rgmii_tx_clk_pll \
{rgmii_adapter_inst|rgmii_tx_pll_inst|altpll_component|auto_generated|pll1|clk[0]} \
-phase 225

#################
# I/O clocks #
#################
# rgmii rx physical clock
create_clock -name fpga_rgmii_rx_clk -period 8.0 -waveform {0 4} [get_ports {rgmii_rx_clk}]

# rgmii rx virtual clock
create_clock -name virt_rgmii_rx_clk -period 8.0 

# rgmii tx physical clock
create_generated_clock -name fpga_rgmii_tx_clk \
-source [get_pins {rgmii_adapter_inst|rgmii_tx_pll_inst|altpll_component|auto_generated|pll1|clk[0]}] \
[get_ports {rgmii_gtx_clk}]

#######################
# Asynchronous groups #
#######################
set_clock_groups -asynchronous \
-group {virt_rgmii_rx_clk fpga_rgmii_rx_clk rgmii_rx_clk_pll} \
-group {fpga_rgmii_tx_clk rgmii_tx_clk_pll clk_125m} 
#-group {clk_100m} \
#-group {clk_50m}

#####################
# Input constraints #
#####################

set_input_delay -clock virt_rgmii_rx_clk -min 1.5 [get_ports {rgmii_rx_dat[*] rgmii_rx_ctl}]
set_input_delay -clock virt_rgmii_rx_clk -max 2.5 [get_ports {rgmii_rx_dat[*] rgmii_rx_ctl}]
set_input_delay -clock virt_rgmii_rx_clk -min 1.5 [get_ports {rgmii_rx_dat[*] rgmii_rx_ctl}] -clock_fall -add_delay
set_input_delay -clock virt_rgmii_rx_clk -max 2.5 [get_ports {rgmii_rx_dat[*] rgmii_rx_ctl}] -clock_fall -add_delay

set_multicycle_path 1 -from        [get_clocks virt_rgmii_rx_clk] -to       [get_clocks rgmii_rx_clk_pll] 
set_multicycle_path 0 -hold -from  [get_clocks virt_rgmii_rx_clk] -to       [get_clocks rgmii_rx_clk_pll] 

set_false_path -setup -rise_from   [get_clocks virt_rgmii_rx_clk] -fall_to  [get_clocks rgmii_rx_clk_pll]
set_false_path -setup -fall_from   [get_clocks virt_rgmii_rx_clk] -rise_to  [get_clocks rgmii_rx_clk_pll]
set_false_path -hold  -rise_from   [get_clocks virt_rgmii_rx_clk] -rise_to  [get_clocks rgmii_rx_clk_pll]
set_false_path -hold  -fall_from   [get_clocks virt_rgmii_rx_clk] -fall_to  [get_clocks rgmii_rx_clk_pll]

######################
# Output constraints #
######################

# set_multicycle_path 0 -setup -end -rise_from  [get_clocks rgmii_tx_clk_pll] -rise_to [get_clocks fpga_rgmii_tx_clk] 
# set_multicycle_path 0 -setup -end -fall_from  [get_clocks rgmii_tx_clk_pll] -fall_to [get_clocks fpga_rgmii_tx_clk] 

set_output_delay -min -1.0 -clock [get_clocks fpga_rgmii_tx_clk] [get_ports {rgmii_tx_dat[*] rgmii_tx_ctl}]
set_output_delay -max  1.0 -clock [get_clocks fpga_rgmii_tx_clk] [get_ports {rgmii_tx_dat[*] rgmii_tx_ctl}]
set_output_delay -min -1.0 -clock [get_clocks fpga_rgmii_tx_clk] [get_ports {rgmii_tx_dat[*] rgmii_tx_ctl}] -clock_fall -add_delay
set_output_delay -max  1.0 -clock [get_clocks fpga_rgmii_tx_clk] [get_ports {rgmii_tx_dat[*] rgmii_tx_ctl}] -clock_fall -add_delay

set_false_path -rise_from [get_clocks clk_125m] -fall_to [get_clocks fpga_rgmii_tx_clk] -setup
set_false_path -fall_from [get_clocks clk_125m] -rise_to [get_clocks fpga_rgmii_tx_clk] -setup
set_false_path -rise_from [get_clocks clk_125m] -rise_to [get_clocks fpga_rgmii_tx_clk] -hold
set_false_path -fall_from [get_clocks clk_125m] -fall_to [get_clocks fpga_rgmii_tx_clk] -hold

derive_clock_uncertainty
# -1.0 1.5 
#  1.0 2.5 
# -1.0 1.5 
#  1.0 2.5 