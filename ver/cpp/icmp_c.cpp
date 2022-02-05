#include "../hdr/icmp_c.h"

  icmp_c::icmp_c (
    const ipv4_c::ipv4_t    _ipv4_addr,
    const mac_c::mac_addr_t _mac_addr,
    const bool              _verbose,
    const bool              _ipv4_verbose,
    const bool              _mac_verbose
  ) : 
    mac_c (
      _mac_addr,
      _mac_verbose
    ),

    ipv4_c (
      _ipv4_verbose
    )
  {
    dev_mac       = _mac_addr;
    dev_ipv4      = _ipv4_addr;
    verbose       = _verbose;
    error_count   = 0;
    success_count = 0;
  };

  icmp_c::~icmp_c() {
    
  };

  bool icmp_c::icmp_parse (
    std::vector<uint8_t>& pkt,
    icmp_c::icmp_meta_t& meta
  ) {
    if (!mac_c::eth_parse (pkt, meta.mac_hdr))
      return false;
    if (meta.mac_hdr.ethertype != IPV4)
      return false;
    if (meta.mac_hdr.dst_mac != dev_mac)
      return false;
    if (!ipv4_c::ipv4_parse(pkt, meta.ipv4_hdr))
      return false;
    if (meta.ipv4_hdr.proto != ICMP)
      return false;
    if (meta.ipv4_hdr.dst_ip != dev_ipv4)
      return false;

    meta.icmp_hdr.icmp_type   = pkt[0];
    meta.icmp_hdr.icmp_code   = pkt[1];
    meta.icmp_hdr.icmp_cks    = extract_16 (pkt, 2);
    meta.icmp_hdr.icmp_id     = extract_16 (pkt, 4);
    meta.icmp_hdr.icmp_seq    = extract_16 (pkt, 6);
    if (
      meta.icmp_hdr.icmp_type == ICMP_ECHO_REQUEST ||
      meta.icmp_hdr.icmp_type == ICMP_ECHO_REPLY
    )
    return true;
    return false;
  }

  void icmp_c::icmp_generate (std::vector<uint8_t>& pkt, icmp_c::icmp_meta_t& meta) {
    pkt.insert (pkt.begin(), {
      (uint8_t)(meta.icmp_hdr.icmp_type     & 0xff),
      (uint8_t)(meta.icmp_hdr.icmp_code     & 0xff),
      (uint8_t)(meta.icmp_hdr.icmp_cks >> 8 & 0xff),
      (uint8_t)(meta.icmp_hdr.icmp_cks      & 0xff),
      (uint8_t)(meta.icmp_hdr.icmp_id  >> 8 & 0xff),
      (uint8_t)(meta.icmp_hdr.icmp_id       & 0xff),
      (uint8_t)(meta.icmp_hdr.icmp_seq >> 8 & 0xff),
      (uint8_t)(meta.icmp_hdr.icmp_seq      & 0xff)
    });
    pkt.push_back (0x01);
    pkt.push_back (0x02);
    pkt.push_back (0x03);
    pkt.push_back (0x04);
    pkt.push_back (0x05);
    pkt.push_back (0x06);
    // Other prococols
    meta.ipv4_hdr.ver      = 4;
    meta.ipv4_hdr.ihl      = 5;
    meta.ipv4_hdr.qos      = 0;
    meta.ipv4_hdr.len      = pkt.size() + ipv4_c::IPV4_HDR_LEN;
    meta.ipv4_hdr.id       = 0;
    meta.ipv4_hdr.frag     = 0;
    meta.ipv4_hdr.ttl      = 64;
    meta.ipv4_hdr.proto    = ipv4_c::ICMP;
    meta.ipv4_hdr.checksum = 0; // skip the calculation for now
    meta.ipv4_hdr.src_ip   = dev_ipv4;
    //ipv4_hdr.dst_ip   = ; //  externally
    ipv4_c::ipv4_generate(pkt, meta.ipv4_hdr);
    meta.mac_hdr.src_mac = dev_mac;
    meta.mac_hdr.ethertype = mac_c::IPV4;
    mac_c::eth_generate(pkt, meta.mac_hdr);
  }

  void icmp_c::icmp_process (
    std::vector<uint8_t>  pkt_rx,
    bool                  val_rx,
    std::vector<uint8_t>& pkt_tx,
    bool&                 val_tx
  ) {
    icmp_c::icmp_meta_t meta_rx, meta_tx;
    bool rx_ok;
    if (val_rx) 
      rx_ok = icmp_parse(pkt_rx, meta_rx);
    if (rx_ok) {
      if (
      meta_rx.ipv4_hdr.dst_ip == dev_ipv4 &&
      meta_rx.mac_hdr.dst_mac == dev_mac &&
      meta_rx.icmp_hdr.icmp_type == ICMP_ECHO_REQUEST) {
        meta_tx = meta_rx;
        meta_tx.icmp_hdr.icmp_type = ICMP_ECHO_REPLY;
        meta_tx.icmp_hdr.icmp_code = 0;
        meta_tx.icmp_hdr.icmp_cks = meta_rx.icmp_hdr.icmp_cks + 0x0800;
        meta_tx.icmp_hdr.icmp_id  = meta_rx.icmp_hdr.icmp_id;
        meta_tx.icmp_hdr.icmp_seq = meta_rx.icmp_hdr.icmp_seq;
        meta_tx.ipv4_hdr.dst_ip   = meta_rx.ipv4_hdr.src_ip;
        meta_tx.mac_hdr.dst_mac   = meta_rx.mac_hdr.src_mac;
        icmp_generate(pkt_tx, meta_tx);
        val_tx = true;
        if (val_tx) return;
      }
    }
    for (int i = 0; i < entry.size(); i++) {
      if (!entry[i].sent) { 
        meta_tx.icmp_hdr.icmp_type = ICMP_ECHO_REQUEST;
        meta_tx.icmp_hdr.icmp_code = 0;
        meta_tx.icmp_hdr.icmp_cks = 0; // skip for now
        meta_tx.icmp_hdr.icmp_id  = entry[i].icmp_id;
        meta_tx.icmp_hdr.icmp_seq = entry[i].icmp_seq;
        meta_tx.ipv4_hdr.dst_ip = entry[i].ipv4;
        meta_tx.mac_hdr.dst_mac = entry[i].mac;
        icmp_generate(pkt_tx, meta_tx);
        entry[i].sent = true;
        val_tx = true;
        return;
      }
      if (entry[i].sent && !entry[i].done) {
        // timeout occured (no reply in time)
        if (entry[i].timer++ == TIMEOUT_TICKS) {
          entry[i].done    = true;
          entry[i].success = false;
          if (verbose) printf("[icmp] no reply from %d.%d.%d.%d, seq: %d\n", 
            entry[i].ipv4.i[0], entry[i].ipv4.i[1], entry[i].ipv4.i[2], entry[i].ipv4.i[3], entry[i].icmp_seq
          );
        }
        // reply received in time
        else if (
        rx_ok && 
        entry[i].ipv4 == meta_rx.ipv4_hdr.src_ip &&
        entry[i].mac == meta_rx.mac_hdr.src_mac && 
        entry[i].icmp_id == meta_rx.icmp_hdr.icmp_id &&
        entry[i].icmp_seq == meta_rx.icmp_hdr.icmp_seq
        ) {
          entry[i].done    = true;
          entry[i].success = true;
          if (verbose) printf("[icmp]<- reply from from %d.%d.%d.%d, seq: %d\n", 
            entry[i].ipv4.i[0], entry[i].ipv4.i[1], entry[i].ipv4.i[2], entry[i].ipv4.i[3], entry[i].icmp_seq
          );
        }
      }
    }
    val_tx = false;
    return;
  }

    unsigned icmp_c::check () {
      unsigned err_ctr = 0;
      for (int i = 0; i < entry.size(); i++) {
        if (!entry[i].success) err_ctr++;
      }
      return err_ctr;
    }

    /* Attemt to add an ICMP request:
     Add a request to be processed
    */
    bool icmp_c::ping_add (
      ipv4_c::ipv4_t ipv4,
      mac_c::mac_addr_t mac
    ) {
      icmp_entry_t ent;
      ent.done  = false;
      ent.timer = 0;
      ent.ipv4  = ipv4;
      ent.mac   = mac;
      ent.icmp_id = entry.size();
      ent.icmp_seq = 0xdead;
      entry.push_back(ent);
    }
