// Test interface with package parameter widths and 2D arrays in structs
// This caused a segfault in AXI4 AVIP

package test_pkg;
  parameter int DATA_WIDTH = 32;
  parameter int ADDR_WIDTH = 16;
  parameter int LENGTH = 4;

  // Struct with 2D array (like AXI4's transfer_char_s)
  typedef struct {
    bit [ADDR_WIDTH-1:0] addr;
    bit [15:0][DATA_WIDTH-1:0] data;  // 2D packed array
    int count;
  } transfer_s;

  class test_class;
    string name;
    transfer_s tx;

    function new(string n = "");
      name = n;
    endfunction

    task process_transfer(inout transfer_s t);
      t.data[0] = 32'hDEADBEEF;
      t.count = 1;
    endtask
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
  test_class tc;

  initial begin
    tc = new("test");
    tc.process_transfer(tc.tx);
    if (tc.tx.data[0] == 32'hDEADBEEF && tc.tx.count == 1)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
