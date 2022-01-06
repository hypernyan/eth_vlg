module mac_bind (
  input logic       clk,
  input logic       rst,
  
  input logic       val,
  input logic [7:0] dat,

  output mac_addr_t mac,
  output logic      bnd
);
  always_ff @ (posedge clk) begin
    if (rst) begin
      bnd <= 0;
      ctr <= 0;
    end
    else begin
      pkt <= {pkt[LEN-2:0], dat};
      ctr <= (val) ? ctr + 1 : 0;
      if (ctr == 20) begin
        mac <= pkt[5:0];
        if (pkt[5:0] != {6{8'hff}}) bnd <= 1;
      end
    end
  end

endmodule : mac_bind
