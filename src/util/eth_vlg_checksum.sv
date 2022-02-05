module eth_vlg_checksum #(
  parameter int BYTES_POW = 1, // Bits per shift (power of 2) 0 => 1 byte per tick
  parameter int LENGTH_BYTES = 30 // total number of input bytes
)
(
  input logic                               clk,
  input logic                               rst,
  input logic [LENGTH_BYTES-1:0][7:0]       data,
  input logic                               calc,
  input logic  [$clog2(LENGTH_BYTES+1)-1:0] len,
  input logic  [31:0]                       init,
  output logic [15:0]                       cks,
  output logic                              done
);

  localparam int BYTES_PER_SHIFT = 2**BYTES_POW;

  logic [31:0] cks32;
  logic [15:0] cks_hi;
  logic [15:0] cks_lo;
  logic [LENGTH_BYTES-1:0][7:0] shiftreg;
  
  logic [$clog2(LENGTH_BYTES+1)-1:0] ctr;
  
  logic [16:0] cks_sum;

  enum logic [2:0] {
    idle_s,
    shift_s,
    calc_s
  } fsm;

  always_ff @ (posedge clk) begin
    if (rst) begin
      ctr <= 0;
      cks32 <= 0;
      done <= 0;
      fsm <= idle_s;
    end
    else begin
      case (fsm)
        idle_s : begin
          cks32    <= init;
          ctr      <= 0;
          shiftreg <= data;
          if (calc) fsm <= shift_s;
        end
        shift_s : begin
          shiftreg <= shiftreg << BYTES_PER_SHIFT*$bits(byte);
          ctr <= ctr + 1;
          cks32 <= cks32 + shiftreg[LENGTH_BYTES-1-:BYTES_PER_SHIFT];
          if (ctr == (len >> BYTES_POW) - 1) fsm <= calc_s;
        end
        calc_s : begin
          done <= 1;
          cks <= ~(cks_sum[15:0] + cks_sum[16]);
        end
        default :;
      endcase
    end
  end
  

  always_comb begin
    cks_sum = cks32[31:16] + cks32[15:0]; // Calculate actual cks  
    cks_lo = cks32[15:0];
    cks_hi = cks32[31:16];
  end
  
endmodule : eth_vlg_checksum