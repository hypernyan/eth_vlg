import esg_pkg_common::*;

module esg_rom #(
    parameter PRM_COUNT = 8
)
(
    input logic                     clk,
    input [$clog2(PRM_COUNT+1)-1:0] addr,
    output prm_entry_t              entry
);
 
prm_entry_t prm_rom [0:PRM_COUNT-1];

`include "esg_reg_defines.sv"

initial begin

  prm_rom[ADDR_LED_PERIOD].prm    = "period";
  prm_rom[ADDR_LED_PERIOD].min    = 0;
  prm_rom[ADDR_LED_PERIOD].max    = 1000;
  prm_rom[ADDR_LED_PERIOD].units  = "ms";
  prm_rom[ADDR_LED_PERIOD].rights = rw;
  prm_rom[ADDR_LED_PERIOD].is_exe = 0;

  prm_rom[ADDR_LED_BRIGHTNESS].prm    = "bright";
  prm_rom[ADDR_LED_BRIGHTNESS].min    = 0;
  prm_rom[ADDR_LED_BRIGHTNESS].max    = 100;
  prm_rom[ADDR_LED_BRIGHTNESS].units  = "unit";
  prm_rom[ADDR_LED_BRIGHTNESS].rights = rw;
  prm_rom[ADDR_LED_BRIGHTNESS].is_exe = 0;

  prm_rom[ADDR_BLINK_ON].prm     = "blink_on";
  prm_rom[ADDR_BLINK_ON].min     = 0;
  prm_rom[ADDR_BLINK_ON].max     = 1;
  prm_rom[ADDR_BLINK_ON].units   = "";
  prm_rom[ADDR_BLINK_ON].rights  = rw;
  prm_rom[ADDR_BLINK_ON].is_exe  = 1;

  prm_rom[ADDR_ALL_ON].prm     = "all_on";
  prm_rom[ADDR_ALL_ON].min     = 0;
  prm_rom[ADDR_ALL_ON].max     = 1;
  prm_rom[ADDR_ALL_ON].units   = "";
  prm_rom[ADDR_ALL_ON].rights  = rw;
  prm_rom[ADDR_ALL_ON].is_exe  = 1;

  prm_rom[ADDR_ALL_OFF].prm     = "all_off";
  prm_rom[ADDR_ALL_OFF].min     = 0;
  prm_rom[ADDR_ALL_OFF].max     = 1;
  prm_rom[ADDR_ALL_OFF].units   = "";
  prm_rom[ADDR_ALL_OFF].rights  = rw;
  prm_rom[ADDR_ALL_OFF].is_exe  = 1;

  prm_rom[ADDR_0_ON].prm     = "led0_on";
  prm_rom[ADDR_0_ON].min     = 0;
  prm_rom[ADDR_0_ON].max     = 1;
  prm_rom[ADDR_0_ON].units   = "";
  prm_rom[ADDR_0_ON].rights  = rw;
  prm_rom[ADDR_0_ON].is_exe  = 1;

  prm_rom[ADDR_0_OFF].prm     = "led0_off";
  prm_rom[ADDR_0_OFF].min     = 0;
  prm_rom[ADDR_0_OFF].max     = 1;
  prm_rom[ADDR_0_OFF].units   = "";
  prm_rom[ADDR_0_OFF].rights  = rw;
  prm_rom[ADDR_0_OFF].is_exe  = 1;

  prm_rom[ADDR_1_ON].prm     = "led1_on";
  prm_rom[ADDR_1_ON].min     = 0;
  prm_rom[ADDR_1_ON].max     = 1;
  prm_rom[ADDR_1_ON].units   = "";
  prm_rom[ADDR_1_ON].rights  = rw;
  prm_rom[ADDR_1_ON].is_exe  = 1;

  prm_rom[ADDR_1_OFF].prm     = "led1_off";
  prm_rom[ADDR_1_OFF].min     = 0;
  prm_rom[ADDR_1_OFF].max     = 1;
  prm_rom[ADDR_1_OFF].units   = "";
  prm_rom[ADDR_1_OFF].rights  = rw;
  prm_rom[ADDR_1_OFF].is_exe  = 1;
        
end

always @ (posedge clk) entry <= prm_rom[addr]; // readout ROM entry containing info about current parameter

endmodule
