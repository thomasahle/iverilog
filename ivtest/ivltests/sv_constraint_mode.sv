// Test constraint_mode() method on class constraint blocks
// constraint_mode(0) disables a constraint, constraint_mode(1) enables it

class ConstraintClass;
  rand int x;
  rand int y;

  // Named constraint blocks
  constraint c_x_range { x >= 0; x <= 100; }
  constraint c_y_range { y >= 0; y <= 50; }
endclass

module test;
  ConstraintClass obj;
  int passed = 0;
  int failed = 0;
  int i;

  initial begin
    obj = new();

    // Test 1: Verify constraints are enabled by default
    if (obj.c_x_range.constraint_mode() == 1) begin
      $display("PASSED: c_x_range is enabled by default");
      passed++;
    end else begin
      $display("FAILED: c_x_range should be enabled by default");
      failed++;
    end

    if (obj.c_y_range.constraint_mode() == 1) begin
      $display("PASSED: c_y_range is enabled by default");
      passed++;
    end else begin
      $display("FAILED: c_y_range should be enabled by default");
      failed++;
    end

    // Test 2: Disable c_x_range constraint
    obj.c_x_range.constraint_mode(0);

    if (obj.c_x_range.constraint_mode() == 0) begin
      $display("PASSED: c_x_range is now disabled");
      passed++;
    end else begin
      $display("FAILED: c_x_range should be disabled after constraint_mode(0)");
      failed++;
    end

    // Test 3: Re-enable c_x_range constraint
    obj.c_x_range.constraint_mode(1);

    if (obj.c_x_range.constraint_mode() == 1) begin
      $display("PASSED: c_x_range is re-enabled");
      passed++;
    end else begin
      $display("FAILED: c_x_range should be enabled after constraint_mode(1)");
      failed++;
    end

    // Test 4: Disable c_y_range constraint
    obj.c_y_range.constraint_mode(0);

    if (obj.c_y_range.constraint_mode() == 0) begin
      $display("PASSED: c_y_range is now disabled");
      passed++;
    end else begin
      $display("FAILED: c_y_range should be disabled");
      failed++;
    end

    // Verify c_x_range is still enabled (independent constraints)
    if (obj.c_x_range.constraint_mode() == 1) begin
      $display("PASSED: c_x_range is still enabled (independent of c_y_range)");
      passed++;
    end else begin
      $display("FAILED: c_x_range should still be enabled");
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
