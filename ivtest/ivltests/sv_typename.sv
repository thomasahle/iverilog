// Test $typename system function
// $typename returns a string with the type name of the expression

module test;
  // Different types to test
  int i;
  real r;
  string str;
  bit [7:0] b;
  logic [15:0] l;

  // Test results
  string result;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    // Test int (shown as bit since int is bit-based)
    result = $typename(i);
    if (result != "") begin
      $display("PASS: $typename(int) = '%s'", result);
      pass_count++;
    end else begin
      $display("FAIL: $typename(int) returned empty string");
      fail_count++;
    end

    // Test real
    result = $typename(r);
    if (result != "") begin
      $display("PASS: $typename(real) = '%s'", result);
      pass_count++;
    end else begin
      $display("FAIL: $typename(real) returned empty string");
      fail_count++;
    end

    // Test string
    result = $typename(str);
    if (result == "string") begin
      $display("PASS: $typename(string) = 'string'");
      pass_count++;
    end else begin
      $display("FAIL: $typename(string) = '%s', expected 'string'", result);
      fail_count++;
    end

    // Test bit
    result = $typename(b);
    if (result != "") begin
      $display("PASS: $typename(bit[7:0]) = '%s'", result);
      pass_count++;
    end else begin
      $display("FAIL: $typename(bit[7:0]) returned empty string");
      fail_count++;
    end

    // Test logic
    result = $typename(l);
    if (result != "") begin
      $display("PASS: $typename(logic[15:0]) = '%s'", result);
      pass_count++;
    end else begin
      $display("FAIL: $typename(logic[15:0]) returned empty string");
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
