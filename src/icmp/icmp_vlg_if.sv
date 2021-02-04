import eth_vlg_pkg::*;
import icmp_vlg_pkg::*;
import ipv4_vlg_pkg::*;
import mac_vlg_pkg::*;

interface icmp;
  stream_t    strm;
  logic       busy;
  logic       done;
  icmp_meta_t meta;

  modport in  (input  strm, meta, output busy, done);
  modport out (output strm, meta, input  busy, done);
endinterface : icmp
