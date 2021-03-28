`define assert_clk ( arg ) \
    assert property (@(posedge clk) disable iff (rst) arg)