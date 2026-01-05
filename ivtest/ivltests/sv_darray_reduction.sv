// Test dynamic array reduction methods: sum, product, min, max
module test;
  int arr[];
  int s, p, mn, mx;
  int passed = 0;
  int failed = 0;

  initial begin
    // Initialize dynamic array with 5 elements
    arr = new[5];
    arr[0] = 1;
    arr[1] = 2;
    arr[2] = 3;
    arr[3] = 4;
    arr[4] = 5;

    // Test sum()
    s = arr.sum();
    if (s == 15) begin
      $display("PASSED: sum() = %0d (expected 15)", s);
      passed++;
    end else begin
      $display("FAILED: sum() = %0d (expected 15)", s);
      failed++;
    end

    // Test product()
    p = arr.product();
    if (p == 120) begin
      $display("PASSED: product() = %0d (expected 120)", p);
      passed++;
    end else begin
      $display("FAILED: product() = %0d (expected 120)", p);
      failed++;
    end

    // Test min()
    mn = arr.min();
    if (mn == 1) begin
      $display("PASSED: min() = %0d (expected 1)", mn);
      passed++;
    end else begin
      $display("FAILED: min() = %0d (expected 1)", mn);
      failed++;
    end

    // Test max()
    mx = arr.max();
    if (mx == 5) begin
      $display("PASSED: max() = %0d (expected 5)", mx);
      passed++;
    end else begin
      $display("FAILED: max() = %0d (expected 5)", mx);
      failed++;
    end

    // Test with negative numbers
    arr[0] = -10;
    arr[1] = -5;
    arr[2] = 0;
    arr[3] = 5;
    arr[4] = 10;

    // Test sum with negatives
    s = arr.sum();
    if (s == 0) begin
      $display("PASSED: sum() with negatives = %0d (expected 0)", s);
      passed++;
    end else begin
      $display("FAILED: sum() with negatives = %0d (expected 0)", s);
      failed++;
    end

    // Test min with negatives
    mn = arr.min();
    if (mn == -10) begin
      $display("PASSED: min() with negatives = %0d (expected -10)", mn);
      passed++;
    end else begin
      $display("FAILED: min() with negatives = %0d (expected -10)", mn);
      failed++;
    end

    // Test max with negatives
    mx = arr.max();
    if (mx == 10) begin
      $display("PASSED: max() with negatives = %0d (expected 10)", mx);
      passed++;
    end else begin
      $display("FAILED: max() with negatives = %0d (expected 10)", mx);
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
