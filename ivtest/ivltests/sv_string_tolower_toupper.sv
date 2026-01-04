// Test string tolower() and toupper() methods
module test;
  string s1, s2;
  int pass_count = 0;
  int fail_count = 0;

  initial begin
    // Test basic lowercase
    s1 = "Hello World";
    s2 = s1.tolower();
    if (s2 == "hello world") begin
      $display("PASS: tolower() basic");
      pass_count++;
    end else begin
      $display("FAIL: tolower() basic, got '%s'", s2);
      fail_count++;
    end

    // Test basic uppercase
    s2 = s1.toupper();
    if (s2 == "HELLO WORLD") begin
      $display("PASS: toupper() basic");
      pass_count++;
    end else begin
      $display("FAIL: toupper() basic, got '%s'", s2);
      fail_count++;
    end

    // Test already lowercase
    s1 = "already lowercase";
    s2 = s1.tolower();
    if (s2 == "already lowercase") begin
      $display("PASS: tolower() no change needed");
      pass_count++;
    end else begin
      $display("FAIL: tolower() no change needed");
      fail_count++;
    end

    // Test already uppercase
    s1 = "ALREADY UPPERCASE";
    s2 = s1.toupper();
    if (s2 == "ALREADY UPPERCASE") begin
      $display("PASS: toupper() no change needed");
      pass_count++;
    end else begin
      $display("FAIL: toupper() no change needed");
      fail_count++;
    end

    // Test mixed with numbers
    s1 = "Test123ABC";
    s2 = s1.tolower();
    if (s2 == "test123abc") begin
      $display("PASS: tolower() with numbers");
      pass_count++;
    end else begin
      $display("FAIL: tolower() with numbers, got '%s'", s2);
      fail_count++;
    end

    s2 = s1.toupper();
    if (s2 == "TEST123ABC") begin
      $display("PASS: toupper() with numbers");
      pass_count++;
    end else begin
      $display("FAIL: toupper() with numbers, got '%s'", s2);
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
