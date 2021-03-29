
interface icmp;
  import eth_vlg_pkg::*;
  import icmp_vlg_pkg::*;

  stream_t    strm;
  logic       busy;
  logic       done;
  icmp_meta_t meta;

  modport in  (input  strm, meta, output busy, done);
  modport out (output strm, meta, input  busy, done);
  modport sva (input  strm, meta,        busy, done);
endinterface : icmp
