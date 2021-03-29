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
  
  /////////
  // MAC //
  /////////
  phy phy(.*);
  mac mac(.*);

  bind mac_vlg_rx mac_vlg_rx_sva mac_vlg_rx_sva_inst (  
    .clk (clk),
    .rst (rst),
 
    .mac (mac),
    .phy (phy)
  );
  
  ////////////////////
  // TCP TX CONTROL //
  ////////////////////

  //tcp.in_rx       rx,
  rx_ctl       ctl (.*);
 // tcp_data.out_rx data // user inteface (raw TCP stream)
  bind tcp_vlg_rx_ctl tcp_vlg_rx_ctl_sva tcp_vlg_rx_ctl_sva_inst (  
    .clk (clk),
    .rst (rst),

    .ctl (ctl)
  );
  
  ////////////////////
  // TCP RX CONTROL //
  ////////////////////
  bind tcp_vlg_tx_ctl tcp_vlg_tx_ctl_sva tcp_vlg_tx_ctl_sva_inst (  
    .clk      (clk),
    .rst      (rst),
 
    .data_val (data.val),
    .data_cts (data.cts)
  );

endmodule
