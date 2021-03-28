import mac_vlg_pkg::*;
import eth_vlg_pkg::*;

`include "../macros.sv"

module sva (
  input logic       clk,
  input logic       rst,

  input stream_t    strm,
  input mac_meta_t  meta,
  input logic       phy_clk,
  input logic       phy_rst,
  input logic [7:0] phy_dat,
  input logic       phy_val,
  input logic       phy_err,
  input dev_t       dev
);

// --- Top level logic --- 
// - DHCP related -
// DHCP will initialize DORA if 'dhcp_start' goes high for at least 1 tick
// DORA will complete in time by indicating dhcp_success 
// correct IP will be assigned by DHCP server

// - ARP related -
// Logic replies to ARP request correctly
// Logic emits correct ARP requests

endmodule : sva
