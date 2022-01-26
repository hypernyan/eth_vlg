module switch_sim #(
  parameter int W   = 64,
  parameter int MTU = 500,
  parameter int IFG_TICKS = 20,
  parameter int N = 3
)(
  input  logic clk,
  input  logic rst,
  input  logic con,
  input  logic[N-1:0] [7:0] din ,
  input  logic[N-1:0]       vin ,
  output logic[N-1:0] [7:0] dout,
  output logic[N-1:0]       vout
);
  
  logic [N-1:0][7:0] dat;
  logic [N-1:0]      val;
  logic[N-1:0]       vin_oh;
  
  logic [N-1:0][$clog2(W)-1:0] wptr;
  logic [N-1:0][$clog2(W)-1:0] rptr, space;
  
  int widx [N];
  int ridx; 

  logic [N-1:0][$clog2(IFG_TICKS+1)-1:0] ifg_ctr;
  logic [MTU-1:0][7:0] pkt [N];

  logic [MTU-1:0][7:0] buff [W];
  int                  size [W];
  int                  port [W];

  logic empty;
  logic full;
  logic writing;
  logic passing;

  enum logic [2:0] {
    r_idle_s,
    read_s,
    ifg_s
  } rfsm;

  typedef enum logic [2:0] {
    w_idle_s,
    write_s,
    pass_s
  } wfsm_t;

  wfsm_t [N-1:0] wfsm;

  always_ff @ (posedge clk) begin
    dat <= din;
    val <= vin;
  end
  
  eth_vlg_onehot #(
    .W  (N),
    .MSB  (1)
  ) onehot_inst (
	  .i (vin),
	  .o (vin_oh)
  );

  always_comb begin
    for (int g = 0; g < N; g++) begin
      if (wfsm[g] == pass_s) passing = 1;
      else passing = 0;
    end
  end

  always_ff @ (posedge clk) begin
    for (int i = 0; i < N; i++) begin
      if (rst) begin
        wfsm[i] <= w_idle_s;
        wptr = 0;
      end
      else begin
        case (wfsm[i])
          w_idle_s : begin
            widx[i] <= 0;
            if (vin[i]) wfsm[i] <= write_s;
          end
          write_s : begin
            pkt[i][widx[i]] <= dat[i];
            if (!val[i]) begin
              wfsm[i] <= w_idle_s;
              buff[wptr] <= pkt[i];
              size[wptr] <= widx[i];
              port[wptr] <= i;
              wptr = wptr + 1;
            end
            widx[i] <= widx[i] + 1;
          end
          pass_s : begin

          end
          default :;
        endcase
      end
    end
  end
  
  logic [31:0] rng;

  prng prng_inst (
    .clk (clk),
    .rst (rst),
    .in  (1'b0),
    .res (rng)
  );
  
  always_comb begin
    for (int i = 0; i < N; i++) begin
      space   = ~(wptr - rptr);
      empty   = (space == '1);
      full    = (space ==  0);
      writing = (wfsm == write_s);
    end
  end
  
  logic tx;

  always_ff @ (posedge clk) begin
    if (rst) begin
      rfsm <= r_idle_s;
      rptr <= 0;
      ifg_ctr <= 0;
    end
    else begin
      case (rfsm)
        r_idle_s : begin
          ifg_ctr <= 0;
          ridx <= 0;
          vout <= 0;
          dout <= 0;
          if (!empty && !passing) rfsm <= read_s;
        end
        read_s : begin
          if (ridx == size[rptr]) begin
            rfsm <= ifg_s;
            rptr <= rptr + 1;
            vout <= 0;
            //tx <= (rng < 32'hf0000000);
          end
          else begin
            for (int i = 0; i < N; i++) begin
              dout[i] <= buff[rptr][ridx];
              vout[i] <= (port[rptr] == i) ? 0 : 1;
            end
          end
          ridx <= ridx + 1;
        end
        ifg_s : begin
          vout <= 0;
          ifg_ctr <= ifg_ctr + 1;
          if (ifg_ctr == IFG_TICKS) rfsm <= r_idle_s;
        end
        default :;
      endcase
    end
  end

endmodule : switch_sim
