import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

// Hold raw TCP data to be transmitted, free space when ack received
// The logic here resembles a FIFO, but:
// 1. Read address is an input rather than an automatically incremented value
// 2. Space is freed by incrementing 'ack' input
// This is done to be able to retransmit unacked data
module tcp_vlg_tx_buf #(
  parameter D = 16,
  parameter W = 16
)
(
  input  logic         rst,
  input  logic         clk,
  
  input  logic         write,
  input  logic [W-1:0] data_in,

  output logic [D-1:0] space,
  input  logic [D-1:0] addr, // address to read from 
  output logic [W-1:0] data_out,

  input  tcp_num_t     seq,
  input  tcp_num_t     ack,
  
  output logic         f,
  output logic         e
);

logic [D-1:0] ptr;
logic [$bits(tcp_num_t):0] diff;

assign diff = seq - ack;
assign space = (diff[D]) ? 0 : ~diff[D-1:0]; // overflow condition accounted

assign e = (diff == 0);
assign f = (space == 0);

always_ff @ (posedge clk) begin
  if (rst) ptr[D-1:0] <= seq[D-1:0];
  else if (write) ptr <= ptr + 1;
end

reg [W-1:0] mem[(1<<D)-1:0];

always_ff @ (posedge clk) data_out <= mem[addr];

always_ff @ (posedge clk) if (write) mem[ptr] <= data_in;

endmodule : tcp_vlg_tx_buf
