interface udp_data_ifc;
  logic [7:0] dat; // data input
  logic       val; // data valid input
  logic       err; // error for rceive path only
  logic       cts; // transmission clear to send. User should countinue sending current datagram even if '0'

  modport in_rx  (input  dat, val, err);
  modport out_rx (output dat, val, err);
  modport in_tx  (input  dat, val, output cts);
  modport out_tx (output dat, val, input  cts);
  modport sva    (input  dat, val,        cts);
endinterface : udp_data_ifc
