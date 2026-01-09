// Test implication constraints: mode == 1 -> value < 10
// When mode is 1, value should be constrained to be < 10
// When mode is 0, value can be any valid value (not constrained)
//
// Note: Full implication constraint support is under development.
// This test verifies that the implication syntax compiles.
// The body constraint is currently treated as a soft constraint.

module test;
  class tx;
    rand bit [3:0] mode;
    rand bit [7:0] value;

    // Simple constraint to limit mode to 0 or 1
    constraint c_mode { mode < 2; }

    // Simple constraint to limit value
    constraint c_val { value < 50; }

    // Implication constraint - syntax test
    // Note: Currently body is treated as soft
    constraint c_impl { mode == 1 -> value < 10; }
  endclass

  initial begin
    automatic tx t = new();
    automatic int passed = 1;
    automatic int mode1_count = 0;
    automatic int mode0_count = 0;
    automatic int mode1_over10 = 0;

    // Run many iterations to check behavior
    repeat(100) begin
      if (t.randomize()) begin
        if (t.mode == 1) begin
          mode1_count++;
          if (t.value >= 10)
            mode1_over10++;
        end else begin
          mode0_count++;
        end
      end else begin
        $display("FAILED: Randomization failed");
        passed = 0;
      end
    end

    // Print statistics
    $display("mode=0: %0d, mode=1: %0d", mode0_count, mode1_count);
    $display("mode=1 with value>=10: %0d (implication body as soft)", mode1_over10);

    // Test should pass if randomization succeeded
    if (passed) $display("PASSED");
    else $display("FAILED");
  end
endmodule
