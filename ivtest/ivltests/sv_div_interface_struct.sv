// Test division with struct parameter in interface task
package pkg;
  typedef struct {
    bit [1:0] mode;
    int wordSelectPeriod;
    int clockPeriod;
  } cfg_struct_t;
endpackage

import pkg::*;

interface my_bfm(input clk);
  int txNumOfBits;

  task genSclk(input cfg_struct_t configPacketStruct);
    // Division of struct member by constant in interface task
    txNumOfBits = configPacketStruct.wordSelectPeriod / 2;
    $display("txNumOfBits = %0d", txNumOfBits);
  endtask
endinterface

module test;
  reg clk = 0;
  always #5 clk = ~clk;

  my_bfm bfm(clk);

  initial begin
    cfg_struct_t cfg;
    cfg.mode = 2'b01;
    cfg.wordSelectPeriod = 64;
    cfg.clockPeriod = 100;

    #10;
    bfm.genSclk(cfg);

    if (bfm.txNumOfBits == 32)
      $display("PASSED");
    else
      $display("FAILED: got %0d, expected 32", bfm.txNumOfBits);
    $finish;
  end
endmodule
