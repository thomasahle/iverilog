// Test interface with class that imports globals package
// This mimics the AXI4 crash pattern

package globals_pkg;
  parameter int DATA_WIDTH = 32;
  parameter int ADDR_WIDTH = 16;

  typedef struct {
    bit [ADDR_WIDTH-1:0] addr;
    bit [DATA_WIDTH-1:0] data;
  } transfer_s;
endpackage

package master_pkg;
  import globals_pkg::*;

  class master_tx;
    bit [ADDR_WIDTH-1:0] addr;
    bit [DATA_WIDTH-1:0] data;

    function new();
    endfunction
  endclass
endpackage

import globals_pkg::*;

interface test_if(input clk, input rst);
  logic [ADDR_WIDTH-1:0] addr;
  logic [DATA_WIDTH-1:0] data;
  logic valid;
endinterface

module top;
  import master_pkg::*;

  bit clk, rst;
  test_if intf(clk, rst);
  master_tx tx;

  initial begin
    tx = new();
    tx.addr = 16'h1234;
    if (tx.addr == 16'h1234)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
