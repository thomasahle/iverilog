// Test interface with package parameter widths
// This caused a segfault in AXI4 AVIP

package test_pkg;
  parameter int DATA_WIDTH = 32;
  parameter int ADDR_WIDTH = 16;

  typedef struct {
    bit [ADDR_WIDTH-1:0] addr;
    bit [DATA_WIDTH-1:0] data;
  } transfer_s;

  class test_class;
    string name;
    function new(string n = "");
      name = n;
    endfunction
  endclass
endpackage

import test_pkg::*;

interface test_if(input clk, input rst);
  logic [ADDR_WIDTH-1:0] addr;
  logic [DATA_WIDTH-1:0] data;
  logic valid;
endinterface

module top;
  bit clk, rst;
  test_if intf(clk, rst);

  initial begin
    $display("PASSED");
    $finish;
  end
endmodule
