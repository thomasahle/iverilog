// Test $cast with enum types
// $cast should return 1 for valid enum values and 0 for invalid values
module test;
  typedef enum {RED=0, GREEN=1, BLUE=2} color_t;

  initial begin
    color_t c;
    int i;
    bit success;
    int pass_count = 0;
    int test_count = 0;

    // Test 1: Valid cast (value 1 = GREEN)
    test_count++;
    i = 1;
    success = $cast(c, i);
    if (success && c == GREEN) begin
      $display("PASSED: $cast(enum, 1) = GREEN");
      pass_count++;
    end else
      $display("FAILED: $cast(enum, 1) returned %0d, c=%0d", success, c);

    // Test 2: Invalid cast (value 5 out of range)
    test_count++;
    i = 5;
    success = $cast(c, i);
    if (!success) begin
      $display("PASSED: $cast(enum, 5) failed as expected");
      pass_count++;
    end else
      $display("FAILED: $cast(enum, 5) should have failed but got c=%0d", c);

    // Test 3: Valid cast (value 0 = RED)
    test_count++;
    i = 0;
    success = $cast(c, i);
    if (success && c == RED) begin
      $display("PASSED: $cast(enum, 0) = RED");
      pass_count++;
    end else
      $display("FAILED: $cast(enum, 0) returned %0d, c=%0d", success, c);

    // Test 4: Valid cast (value 2 = BLUE)
    test_count++;
    i = 2;
    success = $cast(c, i);
    if (success && c == BLUE) begin
      $display("PASSED: $cast(enum, 2) = BLUE");
      pass_count++;
    end else
      $display("FAILED: $cast(enum, 2) returned %0d, c=%0d", success, c);

    // Test 5: Invalid cast (negative value)
    test_count++;
    i = -1;
    success = $cast(c, i);
    if (!success) begin
      $display("PASSED: $cast(enum, -1) failed as expected");
      pass_count++;
    end else
      $display("FAILED: $cast(enum, -1) should have failed but got c=%0d", c);

    // Summary
    if (pass_count == test_count)
      $display("All %0d tests passed", test_count);
    else
      $display("%0d of %0d tests passed", pass_count, test_count);

    $finish;
  end
endmodule
