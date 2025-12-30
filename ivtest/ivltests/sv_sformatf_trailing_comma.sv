// Test that trailing empty parameters (from trailing commas) are handled gracefully
// This is a common typo that should warn but not error

module test;
  string s;
  int i;
  int passed;

  initial begin
    passed = 1;
    i = 42;

    // Case 1: Trailing comma with no format specifier expecting it
    s = $sformatf("value: %0d", i,);  // Trailing comma creates empty param
    if (s != "value: 42") begin
      $display("FAILED: Case 1 - Expected 'value: 42', got '%s'", s);
      passed = 0;
    end

    // Case 2: Multiple trailing commas
    s = $sformatf("test: %0d", i,,);  // Two trailing commas
    if (s != "test: 42") begin
      $display("FAILED: Case 2 - Expected 'test: 42', got '%s'", s);
      passed = 0;
    end

    // Case 3: Normal case without trailing comma (should work as before)
    s = $sformatf("normal: %0d", i);
    if (s != "normal: 42") begin
      $display("FAILED: Case 3 - Expected 'normal: 42', got '%s'", s);
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
