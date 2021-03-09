// simulates a passive switch with N ports
// after receiving a packet, splits it for all ports except the one which sent it
// if 2 or more packets are sent simultaneously from multiple ports, bufferize them
//      port0
//====> rx tx ---->
//      port1
//----> rx tx ====>
//      port2
//----> rx tx ====>
//__________________
// ---> for idle
// ===> for transmission


module switch_sim #(
  parameter int N = 3,
  parameter int IFG = 10
)(
  input logic clk,
  input logic rst,

  input logic  [N-1:0][7:0] din,
  input logic  [N-1:0]      vin,

  output logic [N-1:0][7:0] dout,
  output logic [N-1:0]      vout
);

  /////////////
  // Receive //
  /////////////
  
  logic [N-1:0] val;
  
  genvar gv;
  byte buff[$][];
  int buff_n[$];
  byte data_tx [];
  int tx_ctr, n_tx, ifg_ctr;
  logic transmitting;
  
  generate
    for (gv = 0; gv < N; gv++) begin : gen_dat
      byte data_rx []; // data received and filled by sim_pkt_former
    end
    for (gv = 0; gv < N; gv++) begin : gen_rx
      sim_pkt_former sim_pkt_former_inst(
        .clk  (clk),
        .rst  (rst),
        .din  (din[gv]),
        .vin  (vin[gv]),
        .data (gen_dat[gv].data_rx),
        .val  (val[gv])
      );
      always @ (posedge clk) begin
        if (val[gv]) buff.push_front(gen_dat[gv].data_rx);
        if (val[gv]) buff_n.push_front(gv);
      end
    end
  endgenerate

  always @ (posedge clk) begin
    if (rst) begin
      transmitting = 0;
      vout = 0;
      dout = 0;
      tx_ctr = 0;
      ifg_ctr = 0;
    end
    if ((buff.size() != 0) && !transmitting) begin
      ifg_ctr = 0;
      data_tx = buff.pop_front();
      n_tx = buff_n.pop_front();
      transmitting = 1;
      tx_ctr = 0;
    end
    else if (transmitting && tx_ctr != data_tx.size()) begin
      for (int i = 0; i < N; i++) begin
        dout[i] = data_tx[tx_ctr];
        vout[i] = ~(i == n_tx);
      end
      tx_ctr = tx_ctr + 1;
    end
    else begin
      ifg_ctr = ifg_ctr + 1;
      if (ifg_ctr == IFG) begin
        transmitting = 0;
        tx_ctr = 0;
      end
      vout = 0;
    end
  end
  
  byte pkt [$];
  bit  pkt_val;

endmodule

module sim_pkt_former (
  input logic clk,
  input logic rst,
  input byte  din,
  input logic vin,
  output byte data[$],
  output bit  val

);

  logic receiving;
  
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

endmodule : sim_pkt_former