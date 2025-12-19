// Test associative array with integer keys
module test;

  // Associative array with int key
  int arr[int];
  int passed;
  int result;
  int i;

  initial begin
    passed = 1;

    $display("Testing associative array with integer keys:");

    // Test exists on empty array
    if (arr.exists(42) != 0) begin
      $display("FAILED: exists on empty array should return 0");
      passed = 0;
    end else
      $display("PASSED: exists on empty array returns 0");

    // Add some entries with integer keys
    arr[10] = 100;
    arr[20] = 200;
    arr[30] = 300;

    // Test num/size
    result = arr.num();
    if (result != 3) begin
      $display("FAILED: num should return 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: num() = %0d", result);

    result = arr.size();
    if (result != 3) begin
      $display("FAILED: size should return 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: size() = %0d", result);

    // Test exists with integer key
    if (arr.exists(20) != 1) begin
      $display("FAILED: exists(20) should return 1");
      passed = 0;
    end else
      $display("PASSED: exists(20) = 1");

    if (arr.exists(99) != 0) begin
      $display("FAILED: exists(99) should return 0");
      passed = 0;
    end else
      $display("PASSED: exists(99) = 0");

    // Test value read
    result = arr[10];
    if (result != 100) begin
      $display("FAILED: arr[10] should be 100, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: arr[10] = %0d", result);

    // Test value write/update
    arr[10] = 111;
    result = arr[10];
    if (result != 111) begin
      $display("FAILED: arr[10] should be 111 after update, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: arr[10] updated to %0d", result);

    // Test delete
    arr.delete(20);
    if (arr.exists(20) != 0) begin
      $display("FAILED: exists after delete should return 0");
      passed = 0;
    end else
      $display("PASSED: delete(20) worked");

    result = arr.num();
    if (result != 2) begin
      $display("FAILED: num after delete should return 2, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: num() after delete = %0d", result);

    // Test with negative keys
    arr[-5] = 500;
    if (arr.exists(-5) != 1) begin
      $display("FAILED: exists(-5) should return 1");
      passed = 0;
    end else
      $display("PASSED: exists(-5) = 1");

    result = arr[-5];
    if (result != 500) begin
      $display("FAILED: arr[-5] should be 500, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: arr[-5] = %0d", result);

    $display("");
    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end

endmodule
