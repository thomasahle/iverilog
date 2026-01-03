// Test string methods (supported ones)
module test;
  string s1, s2, s3;
  int len;
  int errors = 0;

  initial begin
    // Test len()
    s1 = "Hello";
    len = s1.len();
    if (len != 5) begin
      $display("FAILED: len of 'Hello' is %0d, expected 5", len);
      errors++;
    end

    // Test empty string len
    s2 = "";
    if (s2.len() != 0) begin
      $display("FAILED: len of empty string is %0d, expected 0", s2.len());
      errors++;
    end

    // Test string concatenation
    s1 = "Hello";
    s2 = " World";
    s3 = {s1, s2};
    if (s3 != "Hello World") begin
      $display("FAILED: concat = '%s', expected 'Hello World'", s3);
      errors++;
    end

    // Test string comparison
    s1 = "abc";
    s2 = "def";
    if (s1 == s2) begin
      $display("FAILED: 'abc' == 'def' should be false");
      errors++;
    end
    if (s1 != "abc") begin
      $display("FAILED: s1 should equal 'abc'");
      errors++;
    end

    // Test string assignment
    s1 = "test";
    s2 = s1;
    if (s2 != "test") begin
      $display("FAILED: s2 = '%s', expected 'test'", s2);
      errors++;
    end

    // Test $sformatf
    s1 = $sformatf("Value: %0d", 42);
    if (s1 != "Value: 42") begin
      $display("FAILED: sformatf = '%s', expected 'Value: 42'", s1);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
