import eth_vlg_pkg::*;

module eth_vlg_tx_mux #(
    parameter int N = 3,
    parameter int W = 8 // metametaa width
  )
  (
    input logic                 clk,
    input logic                 rst,
    // Mux input
    input  logic   [N-1:0]        rdy, // metaa ready to be transmitted
    output logic   [N-1:0]        req, // metaa request to be transmitted
    output logic   [N-1:0]        acc,
    output logic   [N-1:0]        done,
    input logic    [N-1:0][W-1:0] meta, // Protocol-specific metametaa
    input stream_t [N-1:0]        strm,
    // Mux output
    output logic            rdy_mux,
    input  logic            req_mux,
    input  logic            acc_mux,
    input  logic            done_mux,
    output logic    [W-1:0] meta_mux,
    output stream_t         strm_mux
  );

  wor [$clog2(N+1)-1:0] ind;
  logic [N-1:0] rdy_msb, cur_rdy;

  onehot #(N, 1) onehot_msb_inst (
    .i (cur_rdy),
    .o (rdy_msb)
  );
  
  enum logic {idle_s, active_s} fsm;

  always_ff @ (posedge clk) begin
    if (rst) begin
      meta_mux <= 0;
      strm_mux <= 0;
      fsm      <= idle_s;
      rdy_mux  <= 0;
      cur_rdy  <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          if (rdy != 0) fsm <= active_s;
          cur_rdy <= rdy;
        end
        active_s : begin
          meta_mux <= meta[ind];
          strm_mux <= strm[ind];
          if (done_mux) begin
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
      always_ff @ (posedge clk) begin
        if (rst) begin
          req[i]  <= 0;
          acc[i]  <= 0;
          done[i] <= 0;
        end
        else begin
          req[i]  <= rdy_msb[i] & req_mux;
          acc[i]  <= rdy_msb[i] & acc_mux;
          done[i] <= rdy_msb[i] & done_mux;
        end 
      end
    end
  endgenerate

endmodule : eth_vlg_tx_mux
