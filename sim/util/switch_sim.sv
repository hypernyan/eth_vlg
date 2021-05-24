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


module switch_sim
  import
    pcap_pkg::*;
 #(
  parameter int  N         = 3,
  parameter int  IFG       = 10,
  parameter real LOSS_RATE = 0.01
)
(
  input logic clk,
  input logic rst,
  input logic connected,

  input logic  [N-1:0][7:0] din,
  input logic  [N-1:0]      vin,

  output logic [N-1:0][7:0] dout,
  output logic [N-1:0]      vout
);

  localparam int LOSS_RATE_INT = (LOSS_RATE * 32'hffffffff);
  /////////////
  // Receive //
  /////////////
  
  logic [N-1:0] val;
  
  genvar gv;
  byte buff [$][];
  int buff_n [$];
  byte data_tx [];
  int tx_ctr, n_tx, ifg_ctr;
  logic transmitting;
  
  pcapdump #( 
  	.FILENAME ("pcapdump"),
  	.VERBOSE  (1),
  	.REVERSE  (1)
  ) pcapdump_obj;

  initial pcapdump_obj = new();

  generate
    for (gv = 0; gv < N; gv++) begin : gen_dat
      byte data_rx []; // data received and filled by receiver
    end
    for (gv = 0; gv < N; gv++) begin : gen_rx
      receiver receiver_inst(
        .clk  (clk),
        .rst  (rst),
        .din  (din[gv]),
        .vin  (vin[gv]),
        .data (gen_dat[gv].data_rx),
        .val  (val[gv])
      );
      always_ff @ (posedge clk) begin
        if (val[gv] && (($urandom() >= LOSS_RATE_INT) || !connected)) begin
          buff.push_front(gen_dat[gv].data_rx);
          buff_n.push_front(gv);
        end
      end
    end
  endgenerate

  always_ff @ (posedge clk) begin
    if (rst) begin
      transmitting = 0;
      vout = 0;
      dout = 0;
      tx_ctr = 0;
      ifg_ctr = 0;
    end
    if ((buff.size() != 0) && !transmitting) begin
      ifg_ctr = 0;
      data_tx = buff.pop_back();
      n_tx = buff_n.pop_back();
      pcapdump_obj.write_pkt(data_tx);
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
        data_tx.delete();
        transmitting = 0;
        tx_ctr = 0;
      end
      vout = 0;
    end
  end

endmodule : switch_sim
