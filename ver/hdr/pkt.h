#ifndef PKT_C_H
#define PKT_C_H

#include <stdio.h>
#include <stdlib.h>
#include <fstream>
#include <vector>
#include <list>
#include <iomanip>

class pkt {

  public :
    void receive(int time, uint8_t dat, bool val, int idx);
    void generate();


};

#endif