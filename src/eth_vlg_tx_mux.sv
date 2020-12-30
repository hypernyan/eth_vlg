
module eth_vlg_tx_mux #(
    parameter N = 3,
    parameter W = 8 // Metadata width
  )
  (
    input logic                 clk,
    input logic                 rst,
    // Mux input
    input  logic [N-1:0][7:0]   dat,       // Data vector
    input  logic [N-1:0]        val,       // Data valid available vector
    input  logic [N-1:0]        sof,       // Data start-of-frame vector
    input  logic [N-1:0]        eof,       // Data end-of-frame vector
    input  logic [N-1:0]        rdy,       // Data ready to be transmitted
    output logic [N-1:0]        req,       // Data request to be transmitted
    input        [N-1:0][W-1:0] meta,      // Protocol-specific metadata
    // Mux output
    output logic        [7:0]   dat_mux,
    output logic                val_mux,
    output logic                sof_mux,
    output logic                eof_mux,
    output logic                rdy_mux,
    input  logic                req_mux,
    output logic        [W-1:0] meta_mux
  );

  wor [$clog2(N+1)-1:0] ind;
  logic [N-1:0] rdy_msb, cur_rdy;

  onehot #(N, 1) onehot_msb_inst (
    .i (cur_rdy),
    .o (rdy_msb)
  );
  
  enum logic {idle_s, active_s} fsm;

  always @ (posedge clk) begin
    if (rst) begin
      dat_mux <= 0;
      val_mux <= 0;
      sof_mux <= 0;
      eof_mux <= 0;
      rdy_mux <= 0;
      fsm     <= idle_s;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (rdy != 0) begin
            fsm <= active_s;
          end
          // latch current ready vector. 
          // if other rdy goes high, ignore it for current transcation
          cur_rdy <= rdy;
        end
        active_s : begin
          dat_mux  <= dat[ind];
          val_mux  <= val[ind];
          sof_mux  <= sof[ind];
          eof_mux  <= eof[ind];
          meta_mux <= meta[ind];
          if (eof_mux) begin
            fsm <= idle_s;
            rdy_mux <= 0;
            cur_rdy <= 0;
          end
          else rdy_mux <= rdy_msb[ind];
        end
      endcase
    end
  end

  genvar i;

  generate
    for (i = 0; i < N; i = i + 1) begin : gen
      assign ind = (rdy_msb[i] == 1) ? i : 0;
      always @ (posedge clk) if (rst) req[i] <= 0; else req[i] <= rdy_msb[i] & req_mux;
    end
  endgenerate

endmodule : eth_vlg_tx_mux
