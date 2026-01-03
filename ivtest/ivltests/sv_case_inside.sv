// Test case inside statement with ranges
module test;
  int errors = 0;
  int x;
  int result;

  // Test function using case inside
  function automatic int classify(int val);
    case (val) inside
      [0:3]: return 1;      // Range 0-3
      4, 5: return 2;       // Individual values 4 or 5
      [6:10]: return 3;     // Range 6-10
      [100:200], 300: return 4;  // Range 100-200 or value 300
      default: return 0;    // Default
    endcase
  endfunction

  initial begin
    // Test range [0:3]
    if (classify(0) != 1) begin errors++; $display("FAIL: classify(0) = %0d, expected 1", classify(0)); end
    if (classify(1) != 1) begin errors++; $display("FAIL: classify(1) = %0d, expected 1", classify(1)); end
    if (classify(2) != 1) begin errors++; $display("FAIL: classify(2) = %0d, expected 1", classify(2)); end
    if (classify(3) != 1) begin errors++; $display("FAIL: classify(3) = %0d, expected 1", classify(3)); end

    // Test individual values 4, 5
    if (classify(4) != 2) begin errors++; $display("FAIL: classify(4) = %0d, expected 2", classify(4)); end
    if (classify(5) != 2) begin errors++; $display("FAIL: classify(5) = %0d, expected 2", classify(5)); end

    // Test range [6:10]
    if (classify(6) != 3) begin errors++; $display("FAIL: classify(6) = %0d, expected 3", classify(6)); end
    if (classify(10) != 3) begin errors++; $display("FAIL: classify(10) = %0d, expected 3", classify(10)); end

    // Test combined range and value [100:200], 300
    if (classify(150) != 4) begin errors++; $display("FAIL: classify(150) = %0d, expected 4", classify(150)); end
    if (classify(300) != 4) begin errors++; $display("FAIL: classify(300) = %0d, expected 4", classify(300)); end

    // Test default
    if (classify(-1) != 0) begin errors++; $display("FAIL: classify(-1) = %0d, expected 0", classify(-1)); end
    if (classify(50) != 0) begin errors++; $display("FAIL: classify(50) = %0d, expected 0", classify(50)); end
    if (classify(250) != 0) begin errors++; $display("FAIL: classify(250) = %0d, expected 0", classify(250)); end

    // Test edge cases
    if (classify(99) != 0) begin errors++; $display("FAIL: classify(99) = %0d, expected 0", classify(99)); end
    if (classify(100) != 4) begin errors++; $display("FAIL: classify(100) = %0d, expected 4", classify(100)); end
    if (classify(200) != 4) begin errors++; $display("FAIL: classify(200) = %0d, expected 4", classify(200)); end
    if (classify(201) != 0) begin errors++; $display("FAIL: classify(201) = %0d, expected 0", classify(201)); end

    // Test as statement (not just in function)
    x = 7;
    case (x) inside
      [0:5]: result = 100;
      [6:10]: result = 200;
      default: result = 999;
    endcase
    if (result != 200) begin errors++; $display("FAIL: case x=7 result=%0d, expected 200", result); end

    x = 15;
    case (x) inside
      [0:5]: result = 100;
      [6:10]: result = 200;
      default: result = 999;
    endcase
    if (result != 999) begin errors++; $display("FAIL: case x=15 result=%0d, expected 999", result); end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end
endmodule
