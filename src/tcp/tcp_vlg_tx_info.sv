module tcp_vlg_tx_info 
  import
    tcp_vlg_pkg::*;
#(
  parameter int D = 4
)
(
  input logic clk,
  input logic rst,
  // New packets
  input  tcp_pkt_t     new_pkt,
  input  logic         add,
  input  logic         free,
  // Update packets (scanning logic interface)
  input  logic [D-1:0] ptr,
  input  tcp_pkt_t     pkt_w,
  output tcp_pkt_t     pkt_r,
  input  logic         upd,
  output logic         full
);

  /////////////////////
  // Packet info RAM //
  /////////////////////
  logic [D-1:0] space;
  logic [D-1:0] add_ptr;

  ram_dp_ifc #(
    .AW (D),
    .DW ($bits(tcp_pkt_t))
  ) info (.*);

  eth_vlg_ram_dp #(
    .AW (D),
    .DW ($bits(tcp_pkt_t))
  ) data_ram_inst (info);

  assign info.clk_a = clk;
  assign info.clk_b = clk;
  assign info.rst   = rst;
  // `Add new packet` port
  assign info.a_a = add_ptr[D-1:0];
  assign info.d_a = new_pkt;
  assign info.w_a = add;
  // `Update of remove existing packet`
  assign info.a_b = ptr[D-1:0];
  assign info.d_b = pkt_w;
  assign info.w_b = upd;
  assign pkt_r    = info.q_b;

  // difference between push and pop ptr indicate the space left for
  // individual packets that may be stored in packet info RAM
  always @ (posedge clk) begin
    if (rst) begin
      space <= '1;
      add_ptr <= 0;
    end
    else begin
      case ({add, free})
        2'b10 : space <= space - 1;
        2'b01 : space <= space + 1;
        2'b00, 2'b11 :;
      endcase
      if (add) add_ptr <= add_ptr + 1;
    end
  end

  assign full = (space[D-1:1] == {(D-1){1'b0}});

endmodule : tcp_vlg_tx_info
