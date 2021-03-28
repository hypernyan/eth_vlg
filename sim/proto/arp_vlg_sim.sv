package sim_arp_pkg;

  import arp_vlg_pkg::*;
  import eth_vlg_pkg::*;
  import mac_vlg_pkg::*;
  import mac_vlg_sim::*;
  import base_vlg_sim::*;

  class device_arp_c #(parameter bit VERBOSE = 1) extends mac_vlg_sim_c #();

    typedef struct packed {
      ipv4_t ipv4;
      mac_addr_t mac;
      bit present;
    } sim_arp_entry_t;
    sim_arp_entry_t arp_table [0:2**ARP_TABLE_SIZE-1];

    task automatic arp_proc;
      input  byte data_in [];
      output byte data_out[];
      output bit  ok;
      output bit  send;
      arp_hdr_t hdr;
      arp_parse(data_in, hdr, ok);
      if (!ok) disable arp_proc;
      arp_put(hdr.src_ipv4_addr, hdr.src_mac);
      if (hdr.oper == 1) gen_arp_reply(hdr.src_ipv4_addr, hdr.src_mac, data_out);
    endtask : arp_proc

    // Parse MAC and ARP
    protected task automatic arp_parse;
      input  byte      data_in [];
      output arp_hdr_t arp_hdr;
      output bit       ok = 0;
      byte data_eth[];
      bit fcs_ok;
      mac_hdr_t mac_hdr;
      eth_parse(data_in, data_eth, mac_hdr, fcs_ok);
      if (!fcs_ok) disable arp_parse;
      if (mac_hdr.ethertype != ARP) disable arp_parse;

     // if (data_in.size() != ARP_PACKET_SIZE) disable arp_parse;
      arp_hdr = {>>{data_eth with [0:ARP_PACKET_SIZE-1]}};
      ok = 1;
    endtask : arp_parse

    // Generate ARP and MAC frame
    protected task automatic arp_gen;
      input arp_hdr_t hdr;
      output byte     data []; // generated packet is stored here
      mac_hdr_t       mac_hdr; // header to generate mac frame
      // Task
      //$display("<- cli: ARP request from %d.%d.%d.%d at %h:%h:%h:%h:%h:%h to %d.%d.%d.%d",
      //  dev.ipv4_addr[3],
      //  dev.ipv4_addr[2],
      //  dev.ipv4_addr[1],
      //  dev.ipv4_addr[0],
      //  dev.mac_addr[5],
      //  dev.mac_addr[4],
      //  dev.mac_addr[3],
      //  dev.mac_addr[2],
      //  dev.mac_addr[1],
      //  dev.mac_addr[0],
      //  ipv4_addr[3],
      //  ipv4_addr[2],
      //  ipv4_addr[1],
      //  ipv4_addr[0]
      //);
      byte data_arp [];
      bit padding [0:19];
      {<<{padding}} = {20{8'h00}};
      data_arp = new[48];
      {>>{data_arp with [0:arp_vlg_pkg::ARP_HDR_LEN-1]}} = {>>{hdr}};
  	  data_arp = new[48] (data_arp);
      // Padding 
      data_arp[arp_vlg_pkg::ARP_HDR_LEN:47] = {<<{padding}};
      mac_hdr.ethertype = eth_vlg_pkg::ARP;
      mac_hdr.src_mac = MAC_ADDRESS;
      mac_hdr.dst_mac = MAC_BROADCAST;
      eth_gen(data_arp, data, mac_hdr); // Generate mac packet
    endtask : arp_gen

  	protected task automatic gen_arp_reply;
      input ipv4_t     rem_ipv4;
      input mac_addr_t rem_mac;
  	  output byte data[];
  	  arp_hdr_t hdr;
  	  hdr.hw_type       = 1;
      hdr.proto         = 16'h0800;
      hdr.hlen          = 6;
      hdr.plen          = 4;
      hdr.oper          = 1;
      hdr.src_mac  = MAC_ADDRESS;
      hdr.src_ipv4_addr = IPV4_ADDRESS;
      hdr.dst_mac  = rem_mac;
      hdr.dst_ipv4_addr = rem_ipv4;
      arp_gen(hdr, data);
  	endtask : gen_arp_reply

    // Internal ARP table tasks
    // Add entry to table
    protected task automatic arp_put;
      input ipv4_t ipv4;
      input mac_addr_t mac;
      int free_ptr, mac_ptr, ipv4_ptr;
      bit ipv4_found, mac_found;
      for (int i = 0; i < 2**ARP_TABLE_SIZE; i = i + 1) begin
        if (!arp_table[i].present) free_ptr = i;
        if (arp_table[i].mac == mac && arp_table[i].present) begin
          mac_found = 1;
          mac_ptr = i;
        end
        if (arp_table[i].ipv4 == ipv4 && arp_table[i].present) begin
          ipv4_found = 1;
          ipv4_ptr = i;
        end
      end
      case ({mac_found, ipv4_found})
        2'b00 : begin
          if (VERBOSE) $display("Gateway ARP: Adding entry %d:%d:%d:%d - %h:%h:%h:%h:%h:%h",
  	      ipv4[3], ipv4[2], ipv4[1], ipv4[0],
  	      mac[5], mac[4], mac[3], mac[2], mac[1], mac[0]);
          arp_table[free_ptr].mac     = mac;
          arp_table[free_ptr].ipv4    = ipv4;
          arp_table[free_ptr].present = 1;
        end
        2'b01 : begin
          if (VERBOSE) $display("Gateway ARP: Updating MAC %h:%h:%h:%h:%h:%h for %d:%d:%d:%d",
  	      ipv4[3], ipv4[2], ipv4[1], ipv4[0],
  	      mac[5], mac[4], mac[3], mac[2], mac[1], mac[0]);
          arp_table[ipv4_ptr].mac     = mac;
          arp_table[ipv4_ptr].ipv4    = ipv4;
          arp_table[ipv4_ptr].present = 1;		
        end
        2'b10 : begin
          if (VERBOSE) $display("Gateway ARP: Updating IPv4 %d:%d:%d:%d for %h:%h:%h:%h:%h:%h",
  	      ipv4[3], ipv4[2], ipv4[1], ipv4[0],
  	      mac[5], mac[4], mac[3], mac[2], mac[1], mac[0]);
          arp_table[mac_ptr].mac     = mac;
          arp_table[mac_ptr].ipv4    = ipv4;
          arp_table[mac_ptr].present = 1;
        end
        2'b11 : begin
          if (mac_ptr == ipv4_ptr) begin
          //  if (VERBOSE) $display("Gateway ARP: No need to update");
          end
          else if (ipv4_ptr < mac_ptr) begin
            arp_table[mac_ptr].mac      = 0;
            arp_table[mac_ptr].ipv4     = 0;
            arp_table[mac_ptr].present  = 0;
            arp_table[ipv4_ptr].mac     = mac;
            arp_table[ipv4_ptr].ipv4    = ipv4;
            arp_table[ipv4_ptr].present = 1;
          end
          else if (ipv4_ptr > mac_ptr) begin
            arp_table[ipv4_ptr].mac     = 0;
            arp_table[ipv4_ptr].ipv4    = 0;
            arp_table[ipv4_ptr].present = 0;
            arp_table[mac_ptr].mac      = mac;
            arp_table[mac_ptr].ipv4     = ipv4;
            arp_table[mac_ptr].present  = 1;
          end
        end
      endcase
    endtask : arp_put
  
    // Get ARP of a given IPv4
    protected task automatic arp_get;
      input ipv4_t ipv4;
      output mac_addr_t mac;
      output bit found = 0;
      for (int i = 0; i < 2**ARP_TABLE_SIZE; i = i + 1) begin
        if (arp_table[i].ipv4 == ipv4 && arp_table[i].present) begin
          found = 1;
          mac = arp_table[i].mac;
        end
      end
    endtask : arp_get
  /*
    task automatic arp_request;
      input  ipv4_t     ipv4_addr;
      output mac_addr_t mac_addr;
      input  dev_t      dev;
      output bit        to;
      output bit        bad_frame;
  
      byte data_tx [];
      byte data_rx [];
      bit timed_out;
      int len_tx, len_rx;
      mac_hdr_t mac_hdr;
      arp_hdr_t arp_hdr;
      bit arp_ok;
      arp_gen(arp_hdr, data_tx);
      eth_gen(data_tx, len_tx, mac_hdr); // Generate mac packet
      // receive(clk, d_in, v_in, data_rx, timed_out, ARP_TIMEOUT);
  
      if (timed_out) begin
        $display("xx cli: ARP request timeout.");
        disable arp_request;
      end
  
      else arp_parse(data_rx, arp_hdr, arp_ok);
      // $display("ipv4_addr: %d:%d:%d:%d", ipv4_addr[3], ipv4_addr[2], ipv4_addr[1], ipv4_addr[0]); 
      // $display("mac: %h:%h:%h:%h:%h:%h", mac_addr[5], mac_addr[4], mac_addr[3], mac_addr[2], mac_addr[1], mac_addr[0]);
      to = 0;
    endtask : arp_request
  */
  endclass : device_arp_c

endpackage : sim_arp_pkg