interface flow_ifc;
  logic rdy;   // data ready from to IPv4
  logic req;   // data request for tx when done with header
  logic ack;
  logic done;

  modport in  (input  rdy, output req, ack, done);
  modport out (output rdy, input  req, ack, done);
  modport sva (input  rdy,        req, ack, done);
endinterface : flow_ifc
