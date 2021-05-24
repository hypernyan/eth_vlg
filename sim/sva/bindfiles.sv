`include "../util/clkdef.sv"

module bindfiles;
import mac_vlg_pkg::*;
import eth_vlg_pkg::*;
 
  logic clk;

  always #(`CLK_PERIOD/2) clk <= ~clk;
  
  rst_gen rst_gen_inst (
    .clk (clk),
    .rst (rst)
  );
  
  bind mac_vlg_rx     mac_vlg_rx_sva     mac_vlg_rx_sva_inst     (.*);
  bind ipv4_vlg_rx    ipv4_vlg_rx_sva    ipv4_vlg_rx_sva_inst    (.*);
  bind tcp_vlg_rx_ctl tcp_vlg_rx_ctl_sva tcp_vlg_rx_ctl_sva_inst (.*);
  bind tcp_vlg_tx_ctl tcp_vlg_tx_ctl_sva tcp_vlg_tx_ctl_sva_inst (.*);

endmodule
