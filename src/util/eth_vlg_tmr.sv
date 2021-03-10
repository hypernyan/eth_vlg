module eth_vlg_tmr #(
    parameter int TICKS     = 128,
    parameter bit AUTORESET = 1
  )
  (
    input  logic clk,
    input  logic rst,
    input  logic en,
    input  logic tmr_rst,
    output logic tmr
  );

  logic [$clog2(TICKS)-1:0] ctr;


  always_ff @ (posedge clk) begin
    if (rst) begin
      ctr <= 0;
    end
    else if (en) begin
      ctr <= (ctr == TICKS-1) ? 0 : ctr + 1;
    end
  end
  generate
    if (AUTORESET) begin : gen_autoreset
      always_ff @ (posedge clk) if (rst) tmr <= 0; else tmr <= en ? (ctr == TICKS-1) : 0;
    end
    else begin : gen_no_autoreset
      always_ff @ (posedge clk) if (tmr_rst) tmr <= 0; else if (ctr == TICKS-1) tmr <= en;
    end
  endgenerate

endmodule : eth_vlg_tmr
