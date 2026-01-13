// Test named foreach constraint with != on dynamic arrays
// This tests that constraint c { foreach(data[i]) data[i] != 0; }
// works correctly on dynamic arrays.

class Transaction;
  rand bit [7:0] data[];

  // Named foreach constraint with !=
  constraint c_nonzero {
    foreach(data[i]) data[i] != 0;
  }

  function new();
    data = new[4];
  endfunction
endclass

module test;
  Transaction t;
  int passed;
  int zeros_found_total;
  int iterations;

  initial begin
    passed = 1;
    zeros_found_total = 0;
    iterations = 50;
    t = new();

    // Try randomization many times
    repeat(iterations) begin
      if (!t.randomize() with { data.size() == 4; }) begin
        $display("FAIL: randomize failed");
        passed = 0;
      end else begin
        // Check that no element is zero
        for (int i = 0; i < 4; i++) begin
          if (t.data[i] == 0) begin
            zeros_found_total++;
          end
        end
      end
    end

    // With 50 iterations and 4 elements each, that's 200 values
    // Without the constraint, probability of zero in 8-bit random is 1/256
    // Expected zeros without constraint: 200/256 ≈ 0.78
    // With constraint, should be 0

    if (zeros_found_total == 0 && passed)
      $display("PASSED");
    else
      $display("FAILED - zeros found: %0d", zeros_found_total);
    $finish;
  end
endmodule
