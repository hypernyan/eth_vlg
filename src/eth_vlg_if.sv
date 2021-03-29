import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;
import tcp_vlg_pkg::*;
import eth_vlg_pkg::*;

interface phy;
  logic       clk;
  logic       rst;
  logic [7:0] dat;
  logic       val;
  logic       err;
  
  modport in  (input  clk, rst, dat, val, err);
  modport out (output clk, rst, dat, val, err);
  modport sva (input  clk, rst, dat, val, err);
endinterface : phy

interface flow;
  logic rdy;   // data ready from to IPv4
  logic req;   // data request for tx when done with header
  logic ack;
  logic done;

  modport in  (input  rdy, output req, ack, done);
  modport out (output rdy, input  req, ack, done);
  modport sva (input  rdy,        req, ack, done);
endinterface : flow
