// Test dist constraint with both discrete value and range
// This tests that := weight semantics work correctly when mixing
// discrete values and ranges in the same dist constraint.
//
// Bug: Previously, values from the range would fail constraint
// checking because the equality constraint (100) was rechecked
// without considering the OR logic with ranges.

module test;
  class tx;
    rand bit [7:0] val;

    // Range [1:3] with weight 50 per value (total weight 150)
    // Value 100 with weight 50
    // Expected distribution: ~75% range, ~25% value 100
    constraint c_dist {
      val dist { [1:3] := 50, 100 := 50 };
    }
  endclass

  initial begin
    tx t;
    int count_range, count_100, count_other;
    int passed;

    t = new;
    count_range = 0;
    count_100 = 0;
    count_other = 0;

    repeat (1000) begin
      void'(t.randomize());
      if (t.val >= 1 && t.val <= 3) count_range++;
      else if (t.val == 100) count_100++;
      else count_other++;
    end

    $display("count_range=%0d (in [1:3]) count_100=%0d count_other=%0d",
             count_range, count_100, count_other);

    // With := semantics, range [1:3] has total weight 150 (50 * 3 values)
    // Value 100 has weight 50
    // Total = 200
    // Range should get ~75%, value 100 should get ~25%
    // Allow 50-95% for range, 5-50% for 100 (wide margin for randomness)
    passed = 1;
    if (count_range < 500 || count_range > 950) begin
      $display("FAILED: range count %0d out of expected 500-950", count_range);
      passed = 0;
    end
    if (count_100 < 50 || count_100 > 500) begin
      $display("FAILED: 100 count %0d out of expected 50-500", count_100);
      passed = 0;
    end
    if (count_other > 0) begin
      $display("FAILED: got %0d unexpected values", count_other);
      passed = 0;
    end
    if (passed)
      $display("PASSED");
  end
endmodule
