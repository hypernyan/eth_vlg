#include "adapter.h"

adapter_c::adapter_c (
  size_t RXBUF_SIZE,
  size_t TXBUF_SIZE,
  char ifcname [16]
) {
  gen_crc_table(crc_tbl);
  // defined buffers
  //rxbuf = (unsigned char *) calloc(RXBUF_SIZE, sizeof(char));
  //txbuf = (unsigned char *) calloc(TXBUF_SIZE, sizeof(char));
 // txbuf = (unsigned char *) malloc(TXBUF_SIZE);
  memset(txbuf, 0, TXBUF_SIZE);

  strcpy(ifName, "enp0s25");
  bool opened = open();
  tx_idx = 0;
  rx_idx = 0;
  rx_s = idle_s;
  tx_s = idle_s;
  if (!opened) printf("Failed to open\n");

struct ether_header *eh = (struct ether_header *) txbuf;

}

adapter_c::~adapter_c (

) {

}


  uint32_t adapter_c::fcs (char& b) {
    crc = crc_tbl[(crc ^ b) & 0xff] ^ (crc >> 8);
    return crc;  
  }

  void adapter_c::gen_crc_table (uint32_t (&tbl) [256]) {
    for (uint32_t i = 0; i < 256; i++) {
      uint32_t cur = i;
      for (int j = 0; j < 8;j++) {
        cur = (cur & 1) ? (cur >> 1) ^ CRC_POLY : cur >> 1; 
      }
      tbl[i] = cur;
    }
  }

bool adapter_c::open () {
  bool ok = ((sock = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL))) != -1);
  /* Get the index of the interface to send on */
  memset(&if_idx, 0, sizeof(struct ifreq));
  strncpy(if_idx.ifr_name, ifName, IFNAMSIZ-1);
  if (ioctl(sock, SIOCGIFINDEX, &if_idx) < 0) perror("SIOCGIFINDEX");
  /* Get the MAC address of the interface to send on */
  memset(&if_mac, 0, sizeof(struct ifreq));
  strncpy(if_mac.ifr_name, ifName, IFNAMSIZ-1);
  if (ioctl(sock, SIOCGIFHWADDR, &if_mac) < 0) perror("SIOCGIFHWADDR");
  return ok;
}

ssize_t adapter_c::snd (size_t len) {
 // ssize_t act_len = send(sock, txbuf, len, 0);
// struct ether_header *eh = (struct ether_header *) txbuf;
//
// eh->ether_shost[0] = ((uint8_t *)&if_mac.ifr_hwaddr.sa_data)[0];
//eh->ether_shost[1] = ((uint8_t *)&if_mac.ifr_hwaddr.sa_data)[1];
//eh->ether_shost[2] = ((uint8_t *)&if_mac.ifr_hwaddr.sa_data)[2];
//eh->ether_shost[3] = ((uint8_t *)&if_mac.ifr_hwaddr.sa_data)[3];
//eh->ether_shost[4] = ((uint8_t *)&if_mac.ifr_hwaddr.sa_data)[4];
//eh->ether_shost[5] = ((uint8_t *)&if_mac.ifr_hwaddr.sa_data)[5];
//eh->ether_dhost[0] = 0xde;
//eh->ether_dhost[1] = 0xad;
//eh->ether_dhost[2] = 0xbe;
//eh->ether_dhost[3] = 0xef;
//eh->ether_dhost[4] = 0x00;
//eh->ether_dhost[5] = 0x01;
///* Ethertype field */
//eh->ether_type = htons(ETH_P_IP);
/* Index of the network device */
socket_address.sll_ifindex = if_idx.ifr_ifindex;
/* Address length*/
socket_address.sll_halen = ETH_ALEN;
/* Destination MAC */
socket_address.sll_addr[0] = 0x54;
socket_address.sll_addr[1] = 0xee;
socket_address.sll_addr[2] = 0x75;
socket_address.sll_addr[3] = 0xef;
socket_address.sll_addr[4] = 0x00;
socket_address.sll_addr[5] = 0x01;
/* Packet data */
//txbuf[len++] = 0xde;
//txbuf[len++] = 0xad;
//txbuf[len++] = 0xbe;
//txbuf[len++] = 0xef;
  //if ((txbuf[12] == 0x08) && (txbuf[13] == 0x06)) len = len - 4;
  ssize_t act_len = sendto(sock, txbuf, len, 0, (struct sockaddr*)&socket_address, sizeof(struct sockaddr_ll)) ;

  printf("Attempting to send %d bytes\n", len);
 // memset (txbuf, 0, adapter_c::TXBUF_SIZE);
  printf("Actually sent %d bytes\n", act_len);
  return act_len;
}

ssize_t adapter_c::rcv (void* buf[], size_t len) {

}


/* If using loopback, ARP replies from DUT 
  seem to be ignored by Linux kernel
  Add the entry manually
*/

#define MAC_ADDR_DEF "de:ad:fa:ce:ed:ff"

#define SHELL_ARP_ADD "\
#/bin/bash \n\
echo -e \"\" \n\
echo -e \"


bool adapter_c::tx_proc (char& dat, bool& val, char* buf, ssize_t& len) {
  if (val) buf[tx_idx] = dat;
  switch (tx_s) {
    case (idle_s) : {
      tx_idx = 0;
      pre_tx_ctr = 0;
      if (val) tx_s = pre_s;
    break;
    }
    case (pre_s) : {
      pre_tx_ctr++;
      if (pre_tx_ctr == 7) tx_s = pld_s;
    break;
    }
    case (pld_s) : {
      tx_idx++;
      if (!val) {
        tx_s = idle_s;
        len = tx_idx;
        printf("Packet composed of %d bytes\n", len);
        return true;
      }
    break;
    }
  }
  return false;
}

void adapter_c::rx_proc (char& dat, bool& val) {
  switch (rx_s) {
    case (idle_s) : {
      crc = 0xffffffff;
      fcs_ctr = 0;
      ifg_ctr++;
      val = 0;
      rx_idx = 0;
      pre_rx_ctr = 0;
      if (ifg_ctr > IFG_TICKS) {
        len_rx = recvfrom (sock, rxbuf, 1500/*sizeof(ether_header)*/, 0, NULL, NULL);
        if (len_rx > 0) {
          
          if (!(
            (rxbuf[0] == 0x00) &&
            (rxbuf[1] == 0x00) &&
            (rxbuf[2] == 0x00) &&
            (rxbuf[3] == 0x00) &&
            (rxbuf[4] == 0x00) &&
            (rxbuf[5] == 0x00)
          )) {
            printf("Received %d bytes\n", len_rx);
            rx_s = pre_s;
          } 
        }
      }
      break;
    }
    case (pre_s) : {
      ifg_ctr = 0;
      pre_rx_ctr++;
      val = 1;
      dat = (pre_rx_ctr < 8) ? 0x55 : 0xd5;
      if (pre_rx_ctr == 8) rx_s = pld_s;
      break;
    }
    case (pld_s) : {
      dat = rxbuf[rx_idx++];
      crc = fcs(dat);
     // printf("%02x", rxbuf[rx_idx]);
      val = 1;
      if (rx_idx == len_rx) {
        rx_s = fcs_s;
      }
      //rx_idx++;
      break;
    }
    case (fcs_s) : {
      char cur = (crc >> (fcs_ctr++)*8) & 0xff;
      dat = ~cur;
      if (fcs_ctr < 5) break;
      rx_s = idle_s;
      val = 0;
      break;
    }
  }
}




void adapter_c::proc (
  char& dat_rx,
  bool& val_rx,
  char dat_tx,
  bool val_tx
) {
  ssize_t len_tx;
  //proc_rx (dat_rx, val_rx);
  bool tx_pend = tx_proc (dat_tx, val_tx, txbuf, len_tx);
  rx_proc (dat_rx, val_rx);

  if (tx_pend) snd(len_tx-1);
  tx_pend = false;
}
