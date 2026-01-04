// Test string compare() and icompare() methods
module test;
  string s1, s2;
  int result;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    // Test equal strings
    s1 = "hello";
    s2 = "hello";
    result = s1.compare(s2);
    if (result == 0) begin
      $display("PASS: compare() equal strings");
      pass_count++;
    end else begin
      $display("FAIL: compare() equal strings, got %0d", result);
      fail_count++;
    end

    // Test s1 < s2
    s1 = "apple";
    s2 = "banana";
    result = s1.compare(s2);
    if (result < 0) begin
      $display("PASS: compare() s1 < s2");
      pass_count++;
    end else begin
      $display("FAIL: compare() s1 < s2, got %0d", result);
      fail_count++;
    end

    // Test s1 > s2
    s1 = "zebra";
    s2 = "apple";
    result = s1.compare(s2);
    if (result > 0) begin
      $display("PASS: compare() s1 > s2");
      pass_count++;
    end else begin
      $display("FAIL: compare() s1 > s2, got %0d", result);
      fail_count++;
    end

    // Test case sensitivity in compare()
    s1 = "Hello";
    s2 = "hello";
    result = s1.compare(s2);
    if (result != 0) begin
      $display("PASS: compare() case sensitive");
      pass_count++;
    end else begin
      $display("FAIL: compare() should be case sensitive");
      fail_count++;
    end

    // Test icompare() with different cases
    s1 = "Hello";
    s2 = "hello";
    result = s1.icompare(s2);
    if (result == 0) begin
      $display("PASS: icompare() case insensitive equal");
      pass_count++;
    end else begin
      $display("FAIL: icompare() should be case insensitive, got %0d", result);
      fail_count++;
    end

    // Test icompare() with different strings
    s1 = "APPLE";
    s2 = "banana";
    result = s1.icompare(s2);
    if (result < 0) begin
      $display("PASS: icompare() APPLE < banana");
      pass_count++;
    end else begin
      $display("FAIL: icompare() APPLE should be < banana, got %0d", result);
      fail_count++;
    end

    // Summary
    if (fail_count == 0) begin
      $display("PASSED: All %0d tests passed", pass_count);
    end else begin
      $display("FAILED: %0d passed, %0d failed", pass_count, fail_count);
    end
  end
endmodule
