// Test find(), find_first(), find_last() array locator methods
// These return the actual elements, not indices

module test;
  int arr[$];
  int result[$];
  int pass_count = 0;
  int test_count = 0;

  initial begin
    // Initialize array with some values
    arr = '{10, 20, 30, 20, 40, 20, 50};

    $display("Array: %p", arr);

    // Test find() - returns all matching elements
    test_count++;
    result = arr.find with (item == 20);
    $display("find(item == 20): %p", result);
    if (result.size() == 3 && result[0] == 20 && result[1] == 20 && result[2] == 20) begin
      $display("  PASSED: Found 3 elements with value 20");
      pass_count++;
    end else begin
      $display("  FAILED: Expected 3 elements of value 20, got %0d elements", result.size());
    end

    // Test find_first() - returns queue with first matching element
    test_count++;
    result = arr.find_first with (item == 20);
    $display("find_first(item == 20): %p", result);
    if (result.size() == 1 && result[0] == 20) begin
      $display("  PASSED: Found first element 20");
      pass_count++;
    end else begin
      $display("  FAILED: Expected single element 20, got %0d elements", result.size());
    end

    // Test find_last() - returns queue with last matching element
    test_count++;
    result = arr.find_last with (item == 20);
    $display("find_last(item == 20): %p", result);
    if (result.size() == 1 && result[0] == 20) begin
      $display("  PASSED: Found last element 20");
      pass_count++;
    end else begin
      $display("  FAILED: Expected single element 20, got %0d elements", result.size());
    end

    // Test find() with no matches - should return empty queue
    test_count++;
    result = arr.find with (item == 99);
    $display("find(item == 99): %p", result);
    if (result.size() == 0) begin
      $display("  PASSED: Empty result for non-matching value");
      pass_count++;
    end else begin
      $display("  FAILED: Expected empty result, got %0d elements", result.size());
    end

    // Test find_first() with no matches
    test_count++;
    result = arr.find_first with (item == 99);
    if (result.size() == 0) begin
      $display("  PASSED: find_first with no match returns empty");
      pass_count++;
    end else begin
      $display("  FAILED: find_first should return empty for no match");
    end

    // Test find_last() with no matches
    test_count++;
    result = arr.find_last with (item == 99);
    if (result.size() == 0) begin
      $display("  PASSED: find_last with no match returns empty");
      pass_count++;
    end else begin
      $display("  FAILED: find_last should return empty for no match");
    end

    // Test with single element match
    test_count++;
    result = arr.find with (item == 50);
    if (result.size() == 1 && result[0] == 50) begin
      $display("  PASSED: Single match returns single element");
      pass_count++;
    end else begin
      $display("  FAILED: Single match test");
    end

    // Summary
    if (pass_count == test_count) begin
      $display("PASSED: All %0d tests passed", test_count);
    end else begin
      $display("FAILED: %0d of %0d tests passed", pass_count, test_count);
    end
  end
endmodule
