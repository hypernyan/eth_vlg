module eth_vlg_ram_sp #( 
  parameter AW = 16,
  parameter DW = 16
)
(
  ram_sp_ifc.mem mem_if
);

reg [DW - 1:0] ram [2**AW - 1:0];
initial for (int i = 0; i < 2**AW; i = i + 1) ram[i] = '0;

`ifdef SIMULATION
initial begin

  @ ( negedge mem_if.rst )
  @ ( posedge mem_if.clk )
  $readmemh ( "../../src/verilog/true_dpram_sclk/init.txt", ram );
end
`endif

  always @ ( posedge mem_if.clk ) begin
    if ( mem_if.w ) begin
      ram[ mem_if.a ] <= mem_if.d;
      mem_if.q <= mem_if.d;
    end
    else mem_if.q <= ram[ mem_if.a ];
  end

endmodule : eth_vlg_ram_sp
