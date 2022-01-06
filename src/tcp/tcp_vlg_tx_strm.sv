module tcp_vlg_tx_strm
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int D = 10
)
(
  input  logic          clk,
  input  logic          rst,
  input  logic          pend,
  output logic          send,
  input  logic          sent,
  input  logic          req,
  output tcp_num_t      last_seq,
  input  tcp_pld_info_t pld_info,
  input  tcb_t          tcb,
  output logic [D-1:0]  addr,
  output logic          val,
  output logic          sof,
  output logic          eof,
  output logic          idle
);

  enum logic [2:0] {idle_s, wait_s, strm_s} fsm;
  logic upd_seq;
  length_t ctr_tx;
  tcp_num_t seq_dif;
  always_ff @ (posedge clk) begin
    if (rst) begin
      fsm      <= idle_s;
      send     <= 0;
      idle     <= 1;
      last_seq <= tcb.loc_seq;
      addr     <= tcb.loc_seq[D-1];
      val      <= 0;
      sof      <= 0;
      eof      <= 0;
      ctr_tx   <= 0;
      upd_seq  <= 0;
    end
    else begin
      case (fsm)
        idle_s : begin
          seq_dif <= pld_info.stop - last_seq;
          ctr_tx <= 0;
          addr <= pld_info.start[D-1:0];
          if (pend) begin
            idle <= 0;
            send <= 1;
            fsm <= wait_s;
          end
          else idle <= 1;
        end
        wait_s : begin
          upd_seq <= !seq_dif[31]; // only update last seq if packet's end it's above current local seq
          if (req) begin
            send     <= 0;
            sof <= 1;
            val <= 1;
            addr <= addr + 1;
            fsm <= strm_s;
          end
        end
        strm_s : begin
          ctr_tx <= ctr_tx + 1;
          addr <= addr + 1;
          sof <= 0;
          eof <= (ctr_tx == pld_info.lng - 1);
          if (eof) val <= 0;
          if (sent) begin // tx logic indicates packet was sent
            if (upd_seq) last_seq <= pld_info.stop; // Update last seq that was actually sent
            fsm <= idle_s;
          end
        end
        default :;
      endcase
    end
  end
  
endmodule : tcp_vlg_tx_strm
