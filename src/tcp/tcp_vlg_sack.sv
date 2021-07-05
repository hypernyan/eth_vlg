// TCP SACK logic
// 1. keeps SACK updated by processing incomming packets
// 2. manages receive queue
// 3. decides if it's time to read data from queue if missing segment arrived
// 4. directly interfaces user's receive logic
module tcp_vlg_sack
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int    TIMEOUT           = 1250,
  parameter int    FORCE_ACK_PACKETS = 5, 
  parameter int    RAM_DEPTH         = 5,
  parameter bit    VERBOSE           = 0,
  parameter string DUT_STRING        = ""
)
(
  input  logic          clk,
  input  logic          rst,
  tcp.in_rx             rx,
  input  tcp_stat_t     status,
  input  tcb_t          tcb,     // contains initial loc_ack
  input  logic          init,    // initializa local ack with value from TCB 
  output  tcp_num_t     loc_ack, // current local acknowledgement number. valid after init
  tcp_data.out_rx       data,    // user inteface (received raw TCP stream output)

  output logic          store, // indicate RAM to store current packet

  output tcp_opt_sack_t sack,  // current SACK (always valid)
  output logic          upd    // force send Ack containing updated SACK
);
assign upd = 0; // todo
// up to 4 SACK blocks may be reported by receiver
// 1. a SACK block may be added if the packet starts above current Ack number meaning there is a missing segment below
// 2. a new SACK block is created with borders of the incoming packet (seq, seq + len)
// 3. this new SACK block is compared with all present blocks iteratively as they may be concatenated
//    if concatenation occurs, the old SACK block that is compared with the new SACK block
//    is freed and all remaining SACK blocks are shifted to it's position
// 5. after comaring new SACK block with old SACK blocks, the new SACK block (possibly with updated borders from old SACK blocks) 
//    is placed at position 1 as most recently received blocks are reported first
// 6. though the amount of SACK blocks remembered is set by module's parameter SACK_BLOCKS
//    only four may be reported simultaneously. Newer SACK blocks are deleted as local ack progresses
//    older SACK blocks are repoted then 

// example  :     old      new
// before   : ==[SACK3]==[SACK1]====[SACK2]============
// pkt rx   : ================[-pkt1-]=================
// SACK1    : ==[SACK3]=============[SACK2]============
// cat      : ===========[+new block+]=================
// SACK2    : ==[SACK3]=============[SACK2]============
// cat      : ===========[+++new block++++]============
// SACK3    : ==[SACK3]================================
// cat      : ===========[+++new block++++]============
// SACK4    : not present
// upd sack : ==[SACK2]==[+++++SACK1++++++]============
// pkt rx   : ==[SACK2]==[+++++SACK1++++++]==[-pkt2-]==
// SACK1-4  : ==[SACK2]==[+++++SACK1++++++]==[-pkt2-]==
// add sack : ==[SACK3]==[+++++SACK2++++++]==[SACK1+]==

// observe that if and only if a SACK block and packet 
// contain common sequence byte or if one immediately follows another, they are joined
// for this, left and right bonds of the SACK block 
// for that purpose, compare each SACK block's Left and Right borders with Seq and (Seq+Len) of the packet

// we can only accept blocks that fit in RAM. 
// RAM's starting address equals current Ack number, e.g.:
// 16-bit RAM, current Ack num is 32'h1234abcd
// starting seq is thus 32'h1234abce (or RAM addr 16'habce)
// stop seq (after which packets are dropped) is then 32'h1235abce

  enum logic [5:0] {
    idle_s,
    gap_s,
    cat_s,
    cal_s,
    out_s,
    upd_s
  } fsm;

  logic [31:0] 
    start_gap,
    start_dif, 
    stop_dif,        
    left_dif,
    right_dif,
    stop_gap,
    max_seq,
    min_seq;
    
  tcp_num_t cur_ack;

  tcp_opt_sack_t cur_sack, new_sack;
  logic [2:0] blk_num;
  logic in_order;
  tcp_sack_block_t cur_block, new_block;

  logic out_en;

//                   
//                             idle
//                               |
//                           new packet
//                               |
//                               v 
//                            in order?
//                     +-no-- upd ack? -yes-+
//                     |                    |     
//                     v                    v      
//                    pkt                 update
//                  storable?            ack 
//                     |
//                    yes
//
//
// Notes:
// 1. Local ack is updated only either with an in-order packet's last byte's seq (normal in-order flow) or SACK block being reassembled
// 2. The main FSM (that also calculates local ack) is triggered upon receiving a packet with non-zero payload. All necessary operations are performed shortly after receiving first payload byte by this FSM
// 3. There are two parts of the FSM: one for in order packets and the other for out of order.
// 3.a When receiving in-order packets, after the in-order data has been passed to user, all SACK blocks are checked if they are fully or partially acked by the ack number just that has just incremented
// 5.b Out-of order packets may not result in data release to user as there is still a gap in sequence. Upon receiving such packet, logic may only store it in RAM and update existing SACK blocks
//
//

  ram_if_dp #(RAM_DEPTH, 8) rx_buf (.*);
  ram_dp    #(RAM_DEPTH, 8) rx_buf_inst (rx_buf);

  //////////////////
  // Write blocks //
  //////////////////
  stream_t [1:0] strm;
  always_ff @ (posedge clk) begin
    strm <= {strm[0], rx.strm};
  end

  logic port_flt;

  assign rx_buf.rst   = rst;
  assign rx_buf.clk_a = clk;
  assign rx_buf.clk_b = clk;

  assign port_flt = rx.meta.val && (rx.meta.tcp_hdr.src_port == tcb.rem_port) && (rx.meta.tcp_hdr.dst_port == tcb.loc_port); // Received packet's ports match current connection

  always_ff @ (posedge clk) begin
      rx_buf.d_a <= strm[1].dat;
    if (strm[1].sof && store) begin
      rx_buf.w_a <= 1; 
      rx_buf.a_a <= new_block.left;
    end
    else if (!strm[1].val) rx_buf.w_a <= 0;
    else begin
      rx_buf.a_a <= rx_buf.a_a + 1;
    end
  end

  /////////////////
  // Read blocks //
  /////////////////

  assign rx_buf.a_b = cur_ack[RAM_DEPTH-1:0];

  always_ff @ (posedge clk) begin
    if (rst || init) begin
      cur_ack <= tcb.loc_ack;
    end
    else if (status == tcp_connected) begin
      if (cur_ack != loc_ack) begin // increment current ack till it reaches computed local ack
        out_en <= 1; // and output stored data 1 byte per tick
        cur_ack <= cur_ack + 1;
      end
      else out_en <= 0; // otherwise no new data is available
    end
  end

  // actual receive user data interface
  always_ff @ (posedge clk) begin
    data.val <= out_en; 
    data.dat <= rx_buf.q_b;
  end

  ////////////////////////
  // Manage SACK option //
  ////////////////////////

  // The state machine here listens to incomming TCP headers
  // Based on them it generates SACK option to report to sender
  // And manages actual local acknowledgement number
  // The main idea is to increase acknowledgement number only after an in-order packet is received:
  // i.e. that packet's starting sequence number (from TCP header) equals previous local acknowledgement number 
  // When receiving such in-order packets, local ack increases by at least the length ot the packet.
  // However, if that packet fills a missing segment in local receive queue, local ack is increased to the right edge of that complete SACK block
  // That packet, however may be concatenated with one or more packets. each time we receive a packet 
  // it also generates 'in_order' and 'store' signals
  // 'in_order'
  always_ff @ (posedge clk) begin
    if (rst || init) begin
      loc_ack <= tcb.loc_ack;
      sack     <= 0;
      blk_num  <= 0;
      cur_sack <= 0;
      new_sack <= 0;
      in_order <= 0;
      store    <= 0;
      fsm <= idle_s;
    end
    else begin
      case (fsm)
        idle_s : begin
          store <= 0;
          in_order <= 0;
          new_sack <= 0;
          blk_num  <= 0;
          max_seq  <= cur_ack + 2**(RAM_DEPTH); // maximum sequence number that can be stroed in rx buffer
          min_seq  <= cur_ack;                      // minimum sequence number that can be stroed in rx buffer
          // e.g.:
          // sequence lsbyte | 01 02 03 04 05 06 07 08 09 0a 0b 0c 0d 0e 0f 11 12 13 14 15 16 17 18 19 1a 1b 1c 1d 1e 1f
          // loc ack and RAM | ---------- acked -----------] [0--1--2--3--4--5--6--7--8--9--a--b--c--d--e-f]
          //                 |                      loc ack^ ^start                                    stop^   
          //                                                 [---- store ----] [- store -]          [--- drop ---]
          // we need to check that (packet's seq >= min_seq) and (packet's seq+len <= max_seq)
          // because pkt's seq 
          start_gap <= rx.meta.pkt_start - min_seq; // the gap between local ack and received packet's starting seq
          stop_gap  <= max_seq - rx.meta.pkt_stop;  // the gap between last place in rx RAM and packet's stop seq
          new_block <= {rx.meta.pkt_start, rx.meta.pkt_stop}; // initialize new block with packet's borders
          cur_sack  <= sack;
          if (port_flt && rx.strm.sof && rx.meta.tcp_hdr.tcp_flags.ack) fsm <= gap_s;
        end
        gap_s : begin
          if (new_block.left == loc_ack) in_order <= 1;
          if (!start_gap[31] && !stop_gap[31]) begin
            fsm <= cal_s;
            store <= 1;
          end
          else fsm <= idle_s; // cannot store the packet
        end
        /////////////////////////
        // Concatenation logic //
        /////////////////////////
        cal_s : begin // calculate values necessary for concatenation
          cur_block <= cur_sack.block[0];
          // calculate differences
          left_dif  <= new_block.left  - cur_sack.block[0].left;  // bit[31] means start below left -> concat using pkt's start
          right_dif <= cur_sack.block[0].right - new_block.right; // bit[31] means stop  above right -> concat using pkt's stop
          start_dif <= cur_sack.block[0].right - new_block.left;  // ------[SACK1]---- bit[31] means packet's start is within current sack
          stop_dif  <= new_block.right - cur_sack.block[0].left;  // ---[++++++++[---- bit[31] means packet's stop  is within current sack
                                                                  // ------]+++++++]-- both conditions met -> packet will be concatenated with sack block
          if (blk_num == 3) begin
            fsm <= in_order ? out_s : upd_s;
            if (in_order) loc_ack <= new_block.right; // set local ack as this packet's last seq
          end
          else if (cur_sack.block_pres[0]) fsm <= cat_s; // when a present block was found, try to concatenate it with new_sack.block[0]
          cur_sack.block_pres[0:2] <= cur_sack.block_pres[1:3];
          cur_sack.block[0:2] <= cur_sack.block[1:3];
          blk_num <= blk_num + 1;
        end
        cat_s : begin // concatenate blocks
          fsm <= cal_s;
          if (!start_dif[31] && !stop_dif[31]) begin // merging SACK with packet
            new_block.left  <=  (left_dif[31]) ? new_block.left  : cur_block.left; // if (left_dif[31] )
            new_block.right <= (right_dif[31]) ? new_block.right : cur_block.right;
          end
          else begin
            new_sack.block[1:3] <= {cur_block, new_sack.block[1:2]};
            new_sack.block_pres[1:3] <= {1'b1, new_sack.block_pres[1:2]};
          end
        end
        out_s : begin // check if received packet fills missing gap
          $display("Output available from %h to %h", new_block.left, new_block.right);
          sack.block_pres[0:3] <= {new_sack.block_pres[1:3], 1'b0};  
          sack.block[0:2]      <= {new_sack.block[1:3]};
          fsm <= idle_s;
        end
        upd_s : begin
          sack.block[0:3]      <= (in_order) ? {new_sack.block[1:3],      64'h0} : {new_block, new_sack.block[1:3]     };
          sack.block_pres[0:3] <= (in_order) ? {new_sack.block_pres[1:3], 1'b0}  : {1'b1,      new_sack.block_pres[1:3]};
          fsm <= idle_s;
        end
      endcase
    end
  end

endmodule : tcp_vlg_sack
