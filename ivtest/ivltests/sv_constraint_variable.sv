// Test variable-based constraints
// Constraints like x >= min_val where min_val is a property

class VariableConstraintClass;
  rand int x;
  int min_val;
  int max_val;

  // Constraints using property variables (not constants)
  constraint c_range { x >= min_val; x <= max_val; }
endclass

module test;
  VariableConstraintClass obj;
  int passed = 0;
  int failed = 0;
  int in_range_count;
  int i;

  initial begin
    obj = new();

    // Test 1: Very narrow range [5:10]
    obj.min_val = 5;
    obj.max_val = 10;

    in_range_count = 0;
    for (i = 0; i < 20; i++) begin
      void'(obj.randomize());
      if (obj.x >= obj.min_val && obj.x <= obj.max_val) begin
        in_range_count++;
      end
    end

    if (in_range_count == 20) begin
      $display("PASSED: Test 1 - All 20 values in narrow range [5:10]");
      passed++;
    end else begin
      $display("FAILED: Test 1 - Only %0d/20 values in range [5:10]", in_range_count);
      failed++;
    end

    // Test 2: Change bounds at runtime
    obj.min_val = 1000;
    obj.max_val = 1010;

    in_range_count = 0;
    for (i = 0; i < 20; i++) begin
      void'(obj.randomize());
      if (obj.x >= obj.min_val && obj.x <= obj.max_val) begin
        in_range_count++;
      end
    end

    if (in_range_count == 20) begin
      $display("PASSED: Test 2 - All 20 values in new range [1000:1010]");
      passed++;
    end else begin
      $display("FAILED: Test 2 - Only %0d/20 values in range [1000:1010]", in_range_count);
      failed++;
    end

    // Summary
    $display("\nTotal: %0d passed, %0d failed", passed, failed);
    if (failed == 0)
      $display("ALL TESTS PASSED");
    else
      $display("SOME TESTS FAILED");
  end
endmodule
