// Test soft constraints on array size with division
// This tests the pattern commonly used in I2S AVIP:
// constraint c { soft arr.size() == total / WIDTH; }
`include "uvm_pkg.sv"

module test;
  import uvm_pkg::*;

  class item extends uvm_object;
    rand bit[7:0] data[];
    rand int total;

    // Hard constraint for total range
    constraint total_c { total inside {[16:32]}; }

    // Soft constraint for array size with division
    constraint size_c { soft data.size() == total / 4; }

    function new(string name = "item");
      super.new(name);
    endfunction
  endclass

  initial begin
    item i = new();
    int pass = 1;
    int mismatches = 0;

    // Test randomization multiple times
    for (int n = 0; n < 10; n++) begin
      if (!i.randomize()) begin
        $display("FAILED: randomize failed");
        $finish;
      end

      // Check that size matches expected value
      if (i.data.size() != i.total/4) begin
        mismatches++;
      end
    end

    // Report results
    $display("Tested 10 randomizations, mismatches: %0d", mismatches);

    if (mismatches == 0)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
