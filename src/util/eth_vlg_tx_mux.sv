  module eth_vlg_tx_mux  
    import
      eth_vlg_pkg::*;
  #(
    parameter int N = 3,
    parameter int W = 8 // meta width
  )
  (
    input logic                    clk,
    input logic                    rst,
    // Mux input
    input  logic    [N-1:0]        rdy, // metaa ready to be transmitted
    output logic    [N-1:0]        req, // metaa request to be transmitted
    output logic    [N-1:0]        acc,
    output logic    [N-1:0]        err, // transmission error
    output logic    [N-1:0]        done,
    input  logic    [N-1:0][W-1:0] meta, // Protocol-specific metadata
    input  stream_t [N-1:0]        strm,
    // Mux output
    output logic                   rdy_mux,
    input  logic                   req_mux,
    input  logic                   acc_mux,
    input  logic                   err_mux,
    input  logic                   done_mux,
    output logic           [W-1:0] meta_mux,
    output stream_t                strm_mux
  );

  logic [$clog2(N+1)-1:0] ind;
  logic [N-1:0] rdy_msb, cur_rdy;

  eth_vlg_onehot #(N, 1) onehot_msb_inst (
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
          if (strm_mux.eof || err_mux) begin
            fsm <= idle_s;
            rdy_mux <= 0;
            cur_rdy <= 0;
          end
          else if (strm_mux.val) rdy_mux <= 0;
          else rdy_mux <= rdy_msb[ind];
        end
      endcase
    end
  end

  genvar i;

  always_comb begin
    ind = 0;
    for (int i = 0; i < N; i++) if (rdy_msb[i]) ind = i;
  end
  
  generate
    for (i = 0; i < N; i = i + 1) begin : gen
      always_ff @ (posedge clk) begin
        if (rst) begin
          req[i]  <= 0;
          acc[i]  <= 0;
          err[i]  <= 0;
          done[i] <= 0;
        end
        else begin
          req[i]  <= rdy_msb[i] & req_mux;
          acc[i]  <= rdy_msb[i] & acc_mux;
          err[i]  <= rdy_msb[i] & err_mux;
          done[i] <= rdy_msb[i] & done_mux;
        end 
      end
    end
  endgenerate

endmodule : eth_vlg_tx_mux
