// Test unique() queue method
module test;
  int q[$];
  int result[$];

  initial begin
    // Test 1: Basic unique with duplicates
    q = '{3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5};
    $display("Test 1: q = '{3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5}");
    result = q.unique();
    $display("unique result size=%0d", result.size());
    $display("result[0]=%0d result[1]=%0d result[2]=%0d result[3]=%0d result[4]=%0d result[5]=%0d result[6]=%0d",
             result[0], result[1], result[2], result[3], result[4], result[5], result[6]);

    // Expected: 3, 1, 4, 5, 9, 2, 6 (7 unique elements, preserving first occurrence order)
    if (result.size() == 7 && result[0] == 3 && result[1] == 1 && result[2] == 4 && result[3] == 5 &&
        result[4] == 9 && result[5] == 2 && result[6] == 6)
      $display("PASS: unique() with duplicates");
    else
      $display("FAIL: unique() expected 7 elements: 3,1,4,5,9,2,6");

    // Test 2: All same values
    q = '{7, 7, 7, 7};
    $display("\nTest 2: q = '{7, 7, 7, 7}");
    result = q.unique();
    $display("unique result size=%0d value=%0d", result.size(), result[0]);
    if (result.size() == 1 && result[0] == 7)
      $display("PASS: unique() with all same values");
    else
      $display("FAIL: unique() expected 1 element: 7");

    // Test 3: Already unique
    q = '{1, 2, 3, 4, 5};
    $display("\nTest 3: q = '{1, 2, 3, 4, 5}");
    result = q.unique();
    $display("unique result size=%0d", result.size());
    if (result.size() == 5)
      $display("PASS: unique() with no duplicates");
    else
      $display("FAIL: unique() expected 5 elements");

    // Test 4: Negative values
    q = '{-3, 5, -3, 0, 5, -7};
    $display("\nTest 4: q = '{-3, 5, -3, 0, 5, -7}");
    result = q.unique();
    $display("unique result size=%0d", result.size());
    if (result.size() == 4 && result[0] == -3 && result[1] == 5 && result[2] == 0 && result[3] == -7)
      $display("PASS: unique() with negative values");
    else
      $display("FAIL: unique() expected 4 elements: -3,5,0,-7");

    $display("\nTest completed");
  end
endmodule
