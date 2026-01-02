// Test that inside constraints are enforced
// inside {[0:3]} should generate values in range 0-3

module test;

  class packet;
    rand int value;
    rand int other;

    // Inside constraint with range
    constraint value_c { value inside {[0:3]}; }

    // Inside constraint with discrete values
    constraint other_c { other inside {10, 20, 30, 40}; }
  endclass

  initial begin
    packet p;
    int pass_count;
    int fail_count;

    p = new();
    pass_count = 0;
    fail_count = 0;

    $display("Testing 'inside' constraints:");

    // Test 20 randomizations
    repeat(20) begin
      p.randomize();

      // Check value is in range 0-3
      if (p.value >= 0 && p.value <= 3) begin
        pass_count++;
      end else begin
        fail_count++;
        $display("FAIL: value=%0d (expected 0-3)", p.value);
      end

      // Check other is one of the discrete values
      if (p.other == 10 || p.other == 20 || p.other == 30 || p.other == 40) begin
        // pass
      end else begin
        fail_count++;
        $display("FAIL: other=%0d (expected 10,20,30,40)", p.other);
      end
    end

    if (fail_count == 0)
      $display("PASSED: All %0d randomizations satisfied constraints", pass_count);
    else
      $display("FAILED: %0d failures out of %0d tests", fail_count, pass_count + fail_count);
  end

endmodule
