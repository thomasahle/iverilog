// Test file-scope import before interface/module definition
// This tests that import pkg::*; at file scope works correctly
// when the imported names are used inside interfaces or modules.

package test_pkg;
  parameter int DATA_WIDTH = 32;
  parameter int ADDR_WIDTH = 16;
endpackage

// File-scope import - this should work without causing segfault
import test_pkg::*;

interface test_if (input clk);
  // Use imported parameters in signal declarations
  logic [DATA_WIDTH-1:0] wdata;
  logic [ADDR_WIDTH-1:0] addr;
endinterface

module top;
  logic clk = 0;
  test_if dut(clk);

  initial begin
    // Verify the widths are correct
    if ($bits(dut.wdata) != 32) begin
      $display("FAILED: wdata width = %0d, expected 32", $bits(dut.wdata));
      $finish;
    end
    if ($bits(dut.addr) != 16) begin
      $display("FAILED: addr width = %0d, expected 16", $bits(dut.addr));
      $finish;
    end
    $display("PASSED");
    $finish;
  end
endmodule
