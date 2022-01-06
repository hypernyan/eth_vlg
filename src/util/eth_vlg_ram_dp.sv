module eth_vlg_ram_dp #( 
  parameter AW = 16,
  parameter DW = 16
)
(
  ram_dp_ifc.mem mem_if
);
  /* verilator lint_off MULTIDRIVEN */
  reg [DW - 1:0] ram [2**AW - 1:0];
  /* verilator lint_on MULTIDRIVEN */
  
  // Port A
  always @ ( posedge mem_if.clk_a ) begin
    if ( mem_if.w_a ) begin
      ram[ mem_if.a_a ] <= mem_if.d_a;
      mem_if.q_a <= mem_if.d_a;
    end
    else mem_if.q_a <= ram[ mem_if.a_a ];
  end
  // Port B          
  always @ ( posedge mem_if.clk_b ) begin
    if ( mem_if.w_b ) begin
      ram[ mem_if.a_b ] <= mem_if.d_b;
      mem_if.q_b <= mem_if.d_b;
    end
    else mem_if.q_b <= ram[ mem_if.a_b ];
  end
  
endmodule : eth_vlg_ram_dp
