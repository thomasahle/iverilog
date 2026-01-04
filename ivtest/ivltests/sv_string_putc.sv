// Test string putc() method
module test;
  string s;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    // Test basic putc
    s = "Hello";
    s.putc(0, "J");  // Change 'H' to 'J'
    if (s == "Jello") begin
      $display("PASS: putc(0, 'J') changed 'Hello' to 'Jello'");
      pass_count++;
    end else begin
      $display("FAIL: putc(0, 'J'), got '%s'", s);
      fail_count++;
    end

    // Test putc in middle
    s = "Hello";
    s.putc(2, "x");  // Change 'l' to 'x'
    if (s == "Hexlo") begin
      $display("PASS: putc(2, 'x') changed 'Hello' to 'Hexlo'");
      pass_count++;
    end else begin
      $display("FAIL: putc(2, 'x'), got '%s'", s);
      fail_count++;
    end

    // Test putc at end
    s = "Hello";
    s.putc(4, "a");  // Change last 'o' to 'a'
    if (s == "Hella") begin
      $display("PASS: putc(4, 'a') changed 'Hello' to 'Hella'");
      pass_count++;
    end else begin
      $display("FAIL: putc(4, 'a'), got '%s'", s);
      fail_count++;
    end

    // Test putc with ASCII code
    s = "ABC";
    s.putc(1, 88);  // 88 is ASCII for 'X'
    if (s == "AXC") begin
      $display("PASS: putc(1, 88) changed 'ABC' to 'AXC'");
      pass_count++;
    end else begin
      $display("FAIL: putc(1, 88), got '%s'", s);
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
