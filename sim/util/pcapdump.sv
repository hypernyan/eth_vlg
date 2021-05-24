package pcap_pkg;
  class pcapdump #( 
  	parameter     FILENAME = "pcapdump", 
  	parameter bit VERBOSE  = 1,
  	parameter bit REVERSE  = 1
  ); 

    virtual function automatic bit [15:0] rev_16; input bit [15:0] x; return {x[7:0], x[15:8]}; endfunction
    virtual function automatic bit [31:0] rev_32; input bit [31:0] x; return {x[7:0], x[15:8], x[23:16], x[31:24]}; endfunction

    // Global header
    const bit [31:0] MAGIC_NUMBER  = (REVERSE) ? rev_32(32'ha1b23c4d): 32'ha1b23c4d; 
    const bit [15:0] VERSION_MAJOR = (REVERSE) ? rev_16(16'h0002)    : 16'h0002; 
    const bit [15:0] VERSION_MINOR = (REVERSE) ? rev_16(16'h0004)    : 16'h0004;
    const bit [31:0] THISZONE      = (REVERSE) ? rev_32(32'h00000000): 32'h00000000; 
    const bit [31:0] SIGFIGS       = (REVERSE) ? rev_32(32'h00000000): 32'h00000000; 
    const bit [31:0] SNAPLEN       = (REVERSE) ? rev_32(32'h00000400): 32'h00000400; 
    const bit [31:0] NETWORK       = (REVERSE) ? rev_32(32'h00000001): 32'h00000001;

    int f = 0;
    int a;
    typedef struct packed {
      logic [31:0] secs;
      logic [31:0] nsecs;
    } pcap_time_t;

    function new;
      if (f) $fclose(f);
      f = $fopen({FILENAME, ".pcap"}, "wb");
      write_glb_hdr();
    endfunction : new

    task automatic write_pkt;
      input byte data [];
      write_pkt_hdr($size(data)-8);
      for (int i = 8; i < $size(data); i++) $fwrite(f, "%c", data[i]);
    endtask : write_pkt

    protected task automatic write_glb_hdr;
      if (!f) begin
        $error("pcap dump: Failed to write global header. File not open.");
        disable write_glb_hdr;
      end
      $fwrite(f, 
        "%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c",
         MAGIC_NUMBER[31:24], MAGIC_NUMBER[23:16],  MAGIC_NUMBER[15:8],  MAGIC_NUMBER[7:0],
                                                   VERSION_MAJOR[15:8], VERSION_MAJOR[7:0],
                                                   VERSION_MINOR[15:8], VERSION_MINOR[7:0],
             THISZONE[31:24],     THISZONE[23:16],      THISZONE[15:8],      THISZONE[7:0],
              SIGFIGS[31:24],      SIGFIGS[23:16],       SIGFIGS[15:8],       SIGFIGS[7:0],
              SNAPLEN[31:24],      SNAPLEN[23:16],       SNAPLEN[15:8],       SNAPLEN[7:0],
              NETWORK[31:24],      NETWORK[23:16],       NETWORK[15:8],       NETWORK[7:0]);
    endtask : write_glb_hdr

    protected task automatic write_pkt_hdr;
      input [31:0] len;
      pcap_time_t tim;
      if (!f) begin
        $error("pcap dump: Failed to write packet header. File not open.");
        disable write_pkt_hdr;
      end
      tim = get_time();
      $fwrite(
        f,
        "%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c",
         tim.secs[31:24],  tim.secs[23:16],  tim.secs[15:8],  tim.secs[7:0],
        tim.nsecs[31:24], tim.nsecs[23:16], tim.nsecs[15:8], tim.nsecs[7:0],
                len[7:0],        len[15:8],      len[23:16],     len[31:24], 
                len[7:0],        len[15:8],      len[23:16],     len[31:24]
      );
      $display("Time: %d, Seconds: %d. Nanoseconds: %d, Len: %d", $time, rev_32(tim.secs), rev_32(tim.nsecs), len);
    endtask : write_pkt_hdr

    protected function automatic pcap_time_t get_time;
      pcap_time_t tim;
      tim.secs  = $floor($time/1000000000);
      tim.nsecs = $time - tim.secs*1000000000;
      if (REVERSE) begin
        tim.secs  = rev_32(tim.secs);
        tim.nsecs = rev_32(tim.nsecs);
      end
      return tim;
    endfunction : get_time

  endclass : pcapdump
endpackage : pcap_pkg