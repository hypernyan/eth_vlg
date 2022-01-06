interface tcp_data_ifc;
  logic [7:0] dat; // data input
  logic       val; // data valid input
  logic       err; // error for rceive path only
  logic       cts; // transmission clear to send. user has 1 tick to deassert vin before data is lost
  logic       snd; // force sending all buffd data not waiting for TCP_WAIT_TICKS

  modport in_rx  (input  dat, val, err);
  modport out_rx (output dat, val, err);
  modport in_tx  (input  dat, val, snd, output cts);
  modport out_tx (output dat, val, snd, input  cts);
  modport sva    (input  dat, val, snd,        cts);
endinterface : tcp_data_ifc
