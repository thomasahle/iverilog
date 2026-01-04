// Test string getc() method
module test;
  string s;
  int ch;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    s = "Hello";

    // Test getc(0) - first character 'H' = 72
    ch = s.getc(0);
    if (ch == 72) begin
      $display("PASS: getc(0) returned 'H' (72)");
      pass_count++;
    end else begin
      $display("FAIL: getc(0) expected 72, got %0d", ch);
      fail_count++;
    end

    // Test getc(1) - second character 'e' = 101
    ch = s.getc(1);
    if (ch == 101) begin
      $display("PASS: getc(1) returned 'e' (101)");
      pass_count++;
    end else begin
      $display("FAIL: getc(1) expected 101, got %0d", ch);
      fail_count++;
    end

    // Test getc(4) - last character 'o' = 111
    ch = s.getc(4);
    if (ch == 111) begin
      $display("PASS: getc(4) returned 'o' (111)");
      pass_count++;
    end else begin
      $display("FAIL: getc(4) expected 111, got %0d", ch);
      fail_count++;
    end

    // Test with different string
    s = "abc123";
    ch = s.getc(3);  // '1' = 49
    if (ch == 49) begin
      $display("PASS: getc(3) returned '1' (49)");
      pass_count++;
    end else begin
      $display("FAIL: getc(3) expected 49, got %0d", ch);
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
