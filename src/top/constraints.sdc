
#derive uncertainty
derive_clock_uncertainty
#derive_pll_clocks
# Physical clocks
create_clock -period 40 -name clk_25m         -waveform {0 20} [ get_ports { clk_25m } ]
create_clock -period 8  -name phy_rx_clk      -waveform {0 4}  [ get_ports { phy_rx_clk } ]

# logic domain PLL 
create_generated_clock -name clk_125m         -source {reset_controller_inst|logic_pll_inst|altera_pll_i|general[0].gpll~FRACTIONAL_PLL|refclkin} -multiply_by 5              {reset_controller_inst|logic_pll_inst|altera_pll_i|general[0].gpll~PLL_OUTPUT_COUNTER|divclk}
create_generated_clock -name clk_125m_shift   -source {reset_controller_inst|logic_pll_inst|altera_pll_i|general[0].gpll~FRACTIONAL_PLL|refclkin} -multiply_by 5 -phase 0     {reset_controller_inst|logic_pll_inst|altera_pll_i|general[1].gpll~PLL_OUTPUT_COUNTER|divclk}
create_generated_clock -name clk_10m          -source {reset_controller_inst|logic_pll_inst|altera_pll_i|general[0].gpll~FRACTIONAL_PLL|refclkin} -multiply_by 2 -divide_by 5 {reset_controller_inst|logic_pll_inst|altera_pll_i|general[2].gpll~PLL_OUTPUT_COUNTER|divclk}
# rx domain PLL
create_generated_clock -name eth_rx_latch_clk -source {reset_controller_inst|rx_pll_inst|altera_pll_i|general[0].gpll~FRACTIONAL_PLL|refclkin}                     -phase 90 {reset_controller_inst|rx_pll_inst|altera_pll_i|general[0].gpll~PLL_OUTPUT_COUNTER|divclk}
set_multicycle_path 2 -setup -from [ get_clocks { phy_rx_clk } ] -to [ get_clocks { eth_rx_latch_clk } ]

create_generated_clock -name phy_gtx_clk    -source {reset_controller_inst|logic_pll_inst|altera_pll_i|general[1].gpll~PLL_OUTPUT_COUNTER|divclk} [get_ports {phy_gtx_clk}]
#create_generated_clock -name phy_gtx_clk    -source [ get_ports { clk_25m } ] -multiply_by 5 [get_ports {phy_gtx_clk}]

# SignalTap clock
create_clock -period "30.303 ns" -name {altera_reserved_tck} {altera_reserved_tck}

# Async clock groups
set_clock_groups -asynchronous -group { phy_rx_clk } \
                               -group { clk_125m \
							            clk_25m \
										phy_gtx_clk 
										clk_125m_shift }
										 

# rst_n and rst signals are synchronous to system clock domain
set_false_path  -from [ get_registers { reset_controller_inst|rst_n } ] -to [ get_clocks {phy_rx_clk} ]
set_false_path  -from [ get_registers { reset_controller_inst|rst_n } ] -to [ get_clocks {clk_10m} ]

#Input ports

#set_input_delay -min 1.5 -clock phy_rx_clk [ get_ports { phy_rx_dat[*] } ]
#set_input_delay -max 3.5 -clock phy_rx_clk [ get_ports { phy_rx_dat[*] } ]
##
#set_input_delay -min 1.5 -clock phy_rx_clk [ get_ports { phy_rx_err    } ]
#set_input_delay -max 3.5 -clock phy_rx_clk [ get_ports { phy_rx_err    } ]
##
#set_input_delay -min 1.5 -clock phy_rx_clk [ get_ports { phy_rx_val    } ]
#set_input_delay -max 3.5 -clock phy_rx_clk [ get_ports { phy_rx_val    } ]
## Output ports
#
#set_output_delay -min -0.5 -clock phy_gtx_clk [ get_ports { phy_tx_dat[*] } ]
#set_output_delay -max 2.0  -clock phy_gtx_clk [ get_ports { phy_tx_dat[*] } ]
#
#set_output_delay -min -0.5 -clock phy_gtx_clk [ get_ports { phy_tx_err    } ]
#set_output_delay -max 2.0  -clock phy_gtx_clk [ get_ports { phy_tx_err    } ]
#
#set_output_delay -min -0.5 -clock phy_gtx_clk [ get_ports { phy_tx_val    } ]
#set_output_delay -max 2.0  -clock phy_gtx_clk [ get_ports { phy_tx_val    } ]
#
#set_multicycle_path 2 -setup -from [ get_clocks { clk_125m } ] -to [ get_clocks { phy_gtx_clk } ]
#set_multicycle_path 2 -setup -from [ get_registers { reset_controller:reset_controller_inst|rst_n } ] -to [ get_clocks { phy_gtx_clk } ]
