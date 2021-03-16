parameter START_ADDR = 0;
parameter EXEC_START_ADDR  = 2;
// Parameters
parameter int ADDR_LED_BRIGHTNESS = START_ADDR + 0;
parameter int ADDR_LED_PERIOD     = START_ADDR + 1;
// Executives
parameter int ADDR_BLINK_ON = EXEC_START_ADDR + 0;
parameter int ADDR_ALL_ON   = EXEC_START_ADDR + 1;
parameter int ADDR_ALL_OFF  = EXEC_START_ADDR + 2;
parameter int ADDR_0_ON     = EXEC_START_ADDR + 3;
parameter int ADDR_0_OFF    = EXEC_START_ADDR + 4;
parameter int ADDR_1_ON     = EXEC_START_ADDR + 5;
parameter int ADDR_1_OFF    = EXEC_START_ADDR + 6;

parameter int STOP_ADDR = 8;