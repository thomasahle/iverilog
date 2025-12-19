// Test associative array methods: exists, num/size
// Note: first/next/last/prev require ref parameters which need special handling
module test;

  // Standalone associative array with string key
  int arr[string];
  int passed;
  int result;

  initial begin
    passed = 1;

    $display("Testing standalone associative array with string keys:");

    // Test exists on empty array
    if (arr.exists("key1") != 0) begin
      $display("FAILED: exists on empty array should return 0");
      passed = 0;
    end else
      $display("PASSED: exists on empty array returns 0");

    // Add some entries
    arr["alpha"] = 100;
    arr["beta"] = 200;
    arr["gamma"] = 300;

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

    // Test exists with string key
    if (arr.exists("beta") != 1) begin
      $display("FAILED: exists('beta') should return 1");
      passed = 0;
    end else
      $display("PASSED: exists('beta') = 1");

    if (arr.exists("delta") != 0) begin
      $display("FAILED: exists('delta') should return 0");
      passed = 0;
    end else
      $display("PASSED: exists('delta') = 0");

    // Test delete
    arr.delete("beta");
    if (arr.exists("beta") != 0) begin
      $display("FAILED: exists after delete should return 0");
      passed = 0;
    end else
      $display("PASSED: delete('beta') worked");

    result = arr.num();
    if (result != 2) begin
      $display("FAILED: num after delete should return 2, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: num() after delete = %0d", result);

    $display("");
    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end

endmodule
