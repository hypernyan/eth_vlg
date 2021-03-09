

package mac_vlg_sim;

  import mac_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import base_vlg_sim::*;

  typedef struct packed {
    ipv4_t ipv4;
    mac_addr_t mac;
    bit present;
  } sim_arp_entry_t;

  virtual class mac_vlg_sim_c #(
    parameter mac_addr_t MAC_ADDRESS  = 48'hdeadfaced0,
    parameter ipv4_t     IPV4_ADDRESS = {8'd192, 8'd168, 8'd0, 8'd1}
  ) extends base_vlg_sim_c;

    function new ();
    endfunction : new

    function automatic fcs_t gen_fcs;
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
    task automatic check_fcs;
      input  byte data [];
      output bit  ok;
      fcs_t fcs, calc_fcs;
      byte data_fcs[];
      part_select(data, 8, data.size()-5, data_fcs);
     // $display("computing FCS over: %p", data_fcs);
      calc_fcs = gen_fcs(data_fcs);
      fcs = {>>{data with [data.size()-4+:4]}};
     // $display("eth FCS: %h., Calculated: %h", fcs, calc_fcs);
      ok = (fcs == calc_fcs);
    endtask : check_fcs

    ///////////////////////////
    // Parses ethernet frame //
    ///////////////////////////    
    task automatic eth_parse;
      input  byte      data_in [];
      output byte      data    [];
      output mac_hdr_t hdr;
      output bit       fcs_ok = 0;
      int len = data_in.size();
      data = new[len-26]; // 26 bytes are for preamble, header and fcs
      check_fcs(data_in, fcs_ok);
      if (!fcs_ok) disable eth_parse;
      hdr= {>>{data_in with [8:21]}};
      data = {>>{data_in with [22:len-5]}}; // todo: 14 is actual mac hdr len
    endtask : eth_parse
  
    //////////////////////////////
    // Generates ethernet frame //
    //////////////////////////////
    task automatic eth_gen;
      // Ports
      input  byte      data_in  [];
      output byte      data_out [$];
      input  mac_hdr_t mac_hdr;
      // Task
      int len = data_in.size();
      fcs_t fcs;
      byte data_fcs[];
      data_out = new[len+26];
      data_fcs = new[len+14];
      data_fcs = {
        mac_hdr.src_mac[5],
        mac_hdr.src_mac[4],
        mac_hdr.src_mac[3],
        mac_hdr.src_mac[2],
        mac_hdr.src_mac[1],
        mac_hdr.src_mac[0],
        mac_hdr.dst_mac[5],
        mac_hdr.dst_mac[4],
        mac_hdr.dst_mac[3],
        mac_hdr.dst_mac[2],
        mac_hdr.dst_mac[1],
        mac_hdr.dst_mac[0],
        mac_hdr.ethertype[1],
        mac_hdr.ethertype[0], 
        data_in
      };
      fcs = gen_fcs(data_fcs);
  	  data_out = 
        {mac_vlg_pkg::PREAMBLE[7],
         mac_vlg_pkg::PREAMBLE[6],
         mac_vlg_pkg::PREAMBLE[5],
         mac_vlg_pkg::PREAMBLE[4],
         mac_vlg_pkg::PREAMBLE[3],
         mac_vlg_pkg::PREAMBLE[2],
         mac_vlg_pkg::PREAMBLE[1],
         mac_vlg_pkg::PREAMBLE[0],
         data_fcs, fcs[3], fcs[2], fcs[1], fcs[0]};
    endtask : eth_gen
  endclass : mac_vlg_sim_c
endpackage : mac_vlg_sim
