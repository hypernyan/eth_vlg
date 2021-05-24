`include "clkdef.sv"
module receiver #(
  parameter int TIMEOUT = 0
)
(
  input logic      clk,
  input logic      rst,
  input logic[7:0] din,
  input logic      vin,
  output byte      data[$],
  output logic     val
);

  bit receiving;
  int ctr;
  
  time start_time;
  time send_dur;

  generate
    if (TIMEOUT == 0) begin : gen_no_to
      always @(posedge clk) begin
        if (rst) begin
          receiving = 0;
        end
        else begin
          if (vin) begin
            if (!receiving) data.delete();
            receiving = 1;
            data.push_back(din);
          end
          if (!vin && receiving) begin
            receiving = 0;
            val = 1;       
          end
          else val = 0;
        end
      end
    end
    if (TIMEOUT != 0) begin : gen_to
      always @(posedge clk) begin
        if (rst) begin
          receiving = 0;
          ctr = 0;
          val = 0;
        end
        else begin

          if (vin) begin
            if (!receiving) begin
              data.delete();
              start_time = $time();
            end
            receiving = 1;
            data.push_back(din);
            ctr = 0;
            val = 0;
          end
          else if (!vin && receiving) begin
            ctr = ctr + 1;
          end
          else if (!receiving) ctr = 0;
          if (ctr == TIMEOUT) begin
            send_dur = $time() - start_time - (TIMEOUT-1)*(`CLK_PERIOD);
            if (!val) $display("%d bytes received. Estimated throughput %d Mbit/s", $size(data), 1000*($size(data)*(`CLK_PERIOD))/send_dur);
            val = 1;
            receiving = 0;
          end
        end
      end
    end
  endgenerate

endmodule : receiver