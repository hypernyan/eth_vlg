package base_vlg_sim;

  import eth_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import ipv4_vlg_pkg::*;
  
  virtual class base_vlg_sim_c;
  
    localparam string PING_FILE = "ping.txt";

    localparam int
      MTU             = 9000,
      MAC_HDR_LEN     = 26,
      ICMP_HDR_LEN    = 8,
      IPV4_HDR_LEN    = 20,
      TCP_HDR_LEN     = 20,
      ARP_TIMEOUT     = 10000,
      ARP_TABLE_SIZE  = 8,
      ARP_PACKET_SIZE = 28;
  
    localparam byte PREAMBLE [0:7] = {8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'h55, 8'hd5};
  
    protected dev_t dev;
    mac_addr_t MAC_ADDRESS;
    ipv4_t     IPV4_ADDRESS;
  
    ////////////
    // Common //
    ////////////
    protected task automatic shift_data;
      ref byte data [];
      input int data_len;
      input int shift_len;
      for (int i = data_len+1; i > 0; i--) data[i+(shift_len-1)] = data[i-1];
    endtask : shift_data
  
    protected task automatic compare;
      input [7:0] data_a [];
      input [7:0] data_b [];
      output bit equal;
      equal = 0;
      if (data_a.size() != data_b.size()) disable compare;
      for (int i = 0; i < data_a.size(); i++) if (data_a[i] != data_b[i]) disable compare;
      equal = 1;
    endtask : compare
  
    protected task automatic read_file;
      input string file;
      output int   len;
      output byte pkt [0:MTU-1];
      int ctr = 0;
      int f;
      for (int i = 0; i < MTU; i++) pkt[i] = 8'hxx;
      begin
      //  $display("*** PKT GEN *** Reading file %s", file);
        $readmemh(file, pkt);
        while (pkt[ctr] !== 8'hxx) ctr = ctr + 1;
        len = ctr;
        for (int j = ctr; j < MTU; j++) pkt[j] = 0;
      //  $display("*** PKT GEN *** Done reading. Packet length: %d", len);
      end
    endtask : read_file
  
    protected function automatic fcs_t gen_fcs;
      input byte data [];
      bit [31:0] CRC_POLY = 32'hEDB88320;  
      bit [31:0] crc_table [255:0];
      bit [31:0] crc = '1;
      // Generate the table
      for (int i = 0; i < 256; i = i+1) begin
          crc_table[i] = i;
        for (int j = 0; j < 8; j = j+1) crc_table[i] = (crc_table[i][0] && 1'b1) ? (crc_table[i] >> 1) ^ CRC_POLY : crc_table[i] >> 1;
      end
      for (int i = 0; i < data.size(); i = i + 1) crc = crc_table[(crc[7:0]^data[i]) & 8'hff] ^ (crc >> 8); // Calculate The 
      gen_fcs = ~{crc[7:0], crc[15:8], crc[23:16], crc[31:24]};
    endfunction : gen_fcs
  
    // Checks FCS of an ethernet frame
    // Pass raw Ethernet frame with preamble and FCS
    protected task automatic check_fcs;
      input byte data [];
      output bit ok;
      fcs_t fcs, calc_fcs;
      byte data_fcs[];
      part_select(data, 8, data.size()-5, data_fcs);
     // $display("computing FCS over: %p", data_fcs);
      calc_fcs = gen_fcs(data_fcs);
      fcs = {>>{data with [data.size()-4+:4]}};
     // $display("eth FCS: %h., Calculated: %h", fcs, calc_fcs);
      ok = (fcs == calc_fcs);
      if (!ok) $error("Bad FCS: %h. Should be %h", fcs, calc_fcs);
    endtask : check_fcs

  
    //////////////////////////////
    // Generates ethernet frame //
    //////////////////////////////
    function part_select;
      input byte in [];
      input int start;
      input int stop;
      output byte out [];
      // $display("start: %d, stop %d", start, stop);
      if (start > stop) $error("Function part_select: start higher then stop");
      out = new[stop - start];
      out = {>>{in with [start:stop]}};
    endfunction : part_select
  
  endclass : base_vlg_sim_c

endpackage : base_vlg_sim