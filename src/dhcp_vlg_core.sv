module dhcp_vlg_core (
  input logic clk,
  input logic rst,

  input logic ipv4_addr_req     ,
  input ipv4_t ipv4_addr         ,
  output logic ipv4_addr_val     ,
  output logic ipv4_addr_timeout ,
  inptu dev_t dev               ,
  dhcp.in  dhcp_rx,
  dhcp.out dhcp_tx
);

assign dhcp_tx.dhcp_hdr.dhcp_htype   <= 8'h01; // Ethernet
assign dhcp_tx.dhcp_hdr.dhcp_hlen    <= 8'd06; // 6-byte MAC address
assign dhcp_tx.dhcp_hdr.dhcp_hops    <= 8'h00;
assign dhcp_tx.dhcp_hdr.dhcp_xid     <= 32'hdeadbeef; // todo: replace with prbs
assign dhcp_tx.dhcp_hdr.dhcp_secs    <= 16'h0000;
assign dhcp_tx.dhcp_hdr.dhcp_flags   <= 16'h0000;
assign dhcp_tx.dhcp_hdr.dhcp_ciaddr  <= dev.ipv4_addr;
assign dhcp_tx.dhcp_hdr.dhcp_yiaddr  <= 32'h0000000;
assign dhcp_tx.dhcp_hdr.dhcp_siaddr  <= 32'h0000000;
assign dhcp_tx.dhcp_hdr.dhcp_giaddr  <= 32'h0000000;
assign dhcp_tx.dhcp_hdr.dhcp_chaddr  <= {MAC_ADDR, {10{8'h00}}};

enum logic [4:0] {idle_s, discover_s, offer_s, request_s, ack_s};

always @ (posedge clk) begin
  if (fsm_rst) begin
    fsm <= idle_s;

  end
  else begin
    case (fsm)
      idle_s : begin
        if (ipv4_addr_req) fsm <= discover_s;
      end
      discover_s : begin
        dhcp_tx.v <= 1;
        dhcp_tx.dhcp_hdr.dhcp_op     <= DHCP_DISCOVER;
        dhcp_tx.dhcp_hdr.dhcp_sname   <= "nyaaaaaaaaa";
        dhcp_tx.dhcp_hdr.dhcp_file    <= 0;
        dhcp_tx.dhcp_opt_message_type.present <= 1;
        dhcp_tx.dhcp_opt_message_type.;
        dhcp_tx.dhcp_opt_subnet_mask.present <= 0;
        dhcp_tx.dhcp_opt_subnet_mask.;
        dhcp_tx.dhcp_opt_renewal_time.present <= 0;
        dhcp_tx.dhcp_opt_renewal_time.;
        dhcp_tx.dhcp_opt_rebinding_time.present <= 0;
        dhcp_tx.dhcp_opt_rebinding_time.;
        dhcp_tx.dhcp_opt_ip_addr_lease_time.present <= 0;
        dhcp_tx.dhcp_opt_ip_addr_lease_time.;
        dhcp_tx.dhcp_opt_dhcp_server_id.present <= 0;
        dhcp_tx.dhcp_opt_dhcp_server_id.;
        dhcp_tx.dhcp_opt_dhcp_client_id.present <= 0;
        dhcp_tx.dhcp_opt_dhcp_client_id.;
        dhcp_tx.dhcp_opt_router.present <= 0;
        dhcp_tx.dhcp_opt_router.;
        dhcp_tx.dhcp_opt_domain_name_server.present <= 0;
        dhcp_tx.dhcp_opt_domain_name_server.;
        dhcp_tx.dhcp_opt_domain_name.present <= 0;
        dhcp_tx.dhcp_opt_domain_name.;
        dhcp_tx.dhcp_opt_end.present <= 1; // Set which option fields are present

      end
      offer_s : begin
        
      end
      request_s : begin
        
      end
      ack_s : begin
        
      end
    endcase
  end
end
endmodule : dhcp_vlg_core