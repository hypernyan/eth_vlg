`define CLK_PERIOD 8

import mac_vlg_pkg::*;
import icmp_vlg_pkg::*;
import udp_vlg_pkg::*;
import tcp_vlg_pkg::*;
import ip_vlg_pkg::*;
import arp_vlg_pkg::*;
import eth_vlg_pkg::*;

class dhcp_srv_c;
  task acquire(
    ref    logic [7:0] d,
    ref    logic       v,
    output byte        pkt[],
    output int         len,
    ref    bit         pkt_v
  );

  enum bit[2:0] {idle_s, acq_s, crc_s} fsm; 
  bit v_prev;
  byte pkt [1024];
  int ctr = 0;
  pkt_v = 0;
  forever #(`CLK_PERIOD) begin
    v_prev = v;
    case (fsm)
      idle_s : begin
        if (v) begin
		  $display("starting capture");
		  pkt[0] = d;
		  fsm = acq_s;
		end
	  end
      acq_s : begin
		ctr = ctr + 1;
		pkt[ctr] = d;
        if (!v) begin
		  pkt_v = 1;
		  fsm = idle_s;
		  $display ("finished capture: len: %d, %p", ctr, pkt);
        end
	  end
      crc_s : begin
        
      end
    endcase
  end
  endtask : acquire

//  task parse_arp()
//  task parse_()

endclass : pkt_parser_c

endmodule
