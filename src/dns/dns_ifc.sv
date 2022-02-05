interface dns_ifc;
  import eth_vlg_pkg::*;
  import dns_vlg_pkg::*;

  logic       val;
  logic       busy;
  logic       done;
  dns_meta_t  meta;

  modport in  (input  val, meta, output busy, done);
  modport out (output val, meta, input  busy, done);
endinterface : dns_ifc
