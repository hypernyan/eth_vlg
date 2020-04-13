
set_location_assignment PIN_W16  -to phy_gtx_clk
set_location_assignment PIN_E10  -to phy_rx_clk

set_location_assignment PIN_Y17  -to phy_tx_err
set_location_assignment PIN_AA13 -to phy_tx_val
set_location_assignment PIN_Y22  -to phy_tx_dat[7]
set_location_assignment PIN_W22  -to phy_tx_dat[6]
set_location_assignment PIN_Y21  -to phy_tx_dat[5]
set_location_assignment PIN_AA20 -to phy_tx_dat[4]
set_location_assignment PIN_Y20  -to phy_tx_dat[3]
set_location_assignment PIN_AA19 -to phy_tx_dat[2]
set_location_assignment PIN_Y19  -to phy_tx_dat[1]
set_location_assignment PIN_W19  -to phy_tx_dat[0]

set_location_assignment PIN_V20  -to phy_rx_err
set_location_assignment PIN_AB13 -to phy_rx_val
set_location_assignment PIN_AB15 -to phy_rx_dat[7]
set_location_assignment PIN_AA14 -to phy_rx_dat[6]
set_location_assignment PIN_Y14  -to phy_rx_dat[5]
set_location_assignment PIN_U20  -to phy_rx_dat[4]
set_location_assignment PIN_U22  -to phy_rx_dat[3]
set_location_assignment PIN_U21  -to phy_rx_dat[2]
set_location_assignment PIN_Y15  -to phy_rx_dat[1]
set_location_assignment PIN_V21  -to phy_rx_dat[0]

#set_location_assignment PIN_AB21 -to mdc
#set_location_assignment PIN_W21  -to mdio

set_location_assignment PIN_U17  -to phy_rst_n
set_location_assignment PIN_P14  -to phy_pwr_en
                                     
#set_location_assignment PIN_V13  -to auxled_in
#set_location_assignment PIN_T14  -to aled_in
#
#set_location_assignment PIN_T12  -to aled_n
#set_location_assignment PIN_T13  -to aled_p
#set_location_assignment PIN_AB12 -to auxled_n
#set_location_assignment PIN_U13  -to auxled_p
