# Location
set_location_assignment PIN_B8 -to rgmii_rx_clk
set_location_assignment PIN_A5 -to rgmii_rx_ctl
set_location_assignment PIN_B6 -to rgmii_rx_dat[3]
set_location_assignment PIN_A6 -to rgmii_rx_dat[2]
set_location_assignment PIN_B7 -to rgmii_rx_dat[1]
set_location_assignment PIN_A7 -to rgmii_rx_dat[0]

set_location_assignment PIN_D3 -to rgmii_gtx_clk
set_location_assignment PIN_D6 -to rgmii_tx_ctl
set_location_assignment PIN_A2 -to rgmii_tx_dat[3]
set_location_assignment PIN_B3 -to rgmii_tx_dat[2]
set_location_assignment PIN_A3 -to rgmii_tx_dat[1]
set_location_assignment PIN_E6 -to rgmii_tx_dat[0]

set_location_assignment PIN_B4 -to mdc
set_location_assignment PIN_A4 -to mdio
set_location_assignment PIN_J15 -to reset_n

set_location_assignment PIN_J13 -to led[3]  
set_location_assignment PIN_J14 -to led[2]  
set_location_assignment PIN_K15 -to led[1]  
set_location_assignment PIN_L14 -to led[0]  

set_location_assignment PIN_T8  -to gen_clk_125m 
set_location_assignment PIN_E16 -to gen_clk_100m 
set_location_assignment PIN_M15 -to gen_clk_50m

set_global_assignment -name NUM_PARALLEL_PROCESSORS 32
set_global_assignment -name FMAX_REQUIREMENT "125 MHz"
set_global_assignment -name TIMEQUEST_MULTICORNER_ANALYSIS ON
set_global_assignment -name SMART_RECOMPILE ON
set_global_assignment -name MIN_CORE_JUNCTION_TEMP "-40"
set_global_assignment -name MAX_CORE_JUNCTION_TEMP 100
set_global_assignment -name POWER_PRESET_COOLING_SOLUTION "23 MM HEAT SINK WITH 200 LFPM AIRFLOW"
set_global_assignment -name POWER_BOARD_THERMAL_MODEL "NONE (CONSERVATIVE)"
set_global_assignment -name OPTIMIZATION_MODE "HIGH PERFORMANCE EFFORT"
