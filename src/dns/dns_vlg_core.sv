
module dns_vlg_core 
  import 
    eth_vlg_pkg::*,
    dns_vlg_pkg::*,
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*;
#(
  parameter ipv4_t DNS_IP_ADDR_PRI = {8'd8, 8'd8, 8'd8, 8'd8},
  parameter ipv4_t DNS_IP_ADDR_RES = {8'd8, 8'd8, 8'd4, 8'd4},
  parameter int    RETRIES         = 5,
  parameter int    TIMEOUT_SEC     = 5,
  parameter int    DNS_LEASE_SEC   = 5,
  parameter int    REFCLK_HZ       = 125000000,
  parameter bit    VERBOSE         = 1,
  parameter string DUT_STRING      = ""
)
(
  input logic    clk,
  input logic    rst,
  dns_ifc.in     rx,
  dns_ifc.out    tx,
  dns_ctl_ifc.in ctl
);

  enum logic [3:0] {
    idle_s,     // no IP lease, idling
    wait_s,     // wait for UDP become ready, i.e. finished user tx
    query_asm_s,
    query_send_s,
    resp_wait_s, // send DHCPDISCOVER
    lease_s
  } fsm;
  
  logic [$clog2(RETRIES+1)-1:0] fail_cnt;
  logic [$clog2(TIMEOUT_SEC+1)-1:0] tmr;
  
  logic tick;
  logic fsm_rst;
  logic tmr_en;
  logic lease_renewed;

  eth_vlg_tmr #(
    .TICKS (REFCLK_HZ),
    .AUTORESET (1))
  sec_tmr_inst (  
    .clk     (clk),
    .rst     (rst),
    .en      (tmr_en),
    .tmr_rst (1'b0),
    .tmr     (tick) // if timeout counts till timeout
  );

  always_ff @ (posedge clk) fsm_rst <= (rst || (fail_cnt == RETRIES));
  
  always_ff @ (posedge clk) begin
    if (rst || ctl.start) begin
      ctl.ready <= 0;
    end
    else if (ctl.ready || (fail_cnt == RETRIES)) begin
      ctl.ready <= 1;
    end
  end

  logic [$clog2(QRY_LEN+1)-1:0] label_len;
  logic [QRY_LEN-1:0] name;
  
  always_ff @ (posedge clk) begin
    if (fsm_rst) begin
      fsm           <= idle_s;
      fail_cnt      <= 0;
    end
    else begin
      // constant fieldsrx.hdr.dhcp_chaddr == {MAC_ADDR, {10{8'h00}
      tx.meta.dns_ipv4 <= ctl.ipv4_pri;
      // state machine
      case (fsm)
        idle_s : begin
          tx.meta.length <= $bits(dns_hdr_t)/8;
          name <= ctl.name;
          if (ctl.start) begin
            fsm <= wait_s;
          end
        end
        query_asm_s : begin
          tx.meta.length <= tx.meta.length + 1;
          if (tx.meta.length == QRY_LEN) fsm <= query_send_s;
          name[QRY_LEN-1:0] <= name >> $bits(byte);
          if (name[0] != "") tx.meta.length <= tx.meta.length + 1;
          if (name[0] == ".") begin
            tx.meta.qry[QRY_LEN-1] <= label_len;
            label_len <= 0;
          end
          else begin
            tx.meta.qry[QRY_LEN-1] <= name[0];
            label_len <= label_len + 1;
          end
        end
        query_send_s : begin
          if (VERBOSE) begin
            $display("[", DUT_STRING, "]-> Attemting to acquire IP for %s. DNS IP: %d.%d.%d.%d", 
            ctl.name, ctl.ipv4_pri[3], ctl.ipv4_pri[2], ctl.ipv4_pri[1], ctl.ipv4_pri[0]);
          end
          fsm <= resp_wait_s;
          tx.val <= 1;
        end
        resp_wait_s : begin

        end
        default :;
      endcase
    end
  end

endmodule : dns_vlg_core
