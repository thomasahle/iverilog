// Test array locator find/find_first/find_last methods with comparison operators
// These return elements (not indices) that match the comparison

module test;

   int q[$] = '{10, 20, 30, 40, 50};
   int result[$];
   int single[$];
   int passed = 0;
   int failed = 0;

   initial begin
      // Test 1: find with > operator
      result = q.find with (item > 25);
      $display("Test 1: find (item > 25): size=%0d", result.size());
      foreach(result[i]) $display("  result[%0d] = %0d", i, result[i]);
      if (result.size() == 3 && result[0] == 30 && result[1] == 40 && result[2] == 50) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {30, 40, 50}");
         failed++;
      end

      // Test 2: find with < operator
      result = q.find with (item < 25);
      $display("Test 2: find (item < 25): size=%0d", result.size());
      foreach(result[i]) $display("  result[%0d] = %0d", i, result[i]);
      if (result.size() == 2 && result[0] == 10 && result[1] == 20) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {10, 20}");
         failed++;
      end

      // Test 3: find with >= operator
      result = q.find with (item >= 30);
      $display("Test 3: find (item >= 30): size=%0d", result.size());
      foreach(result[i]) $display("  result[%0d] = %0d", i, result[i]);
      if (result.size() == 3 && result[0] == 30 && result[1] == 40 && result[2] == 50) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {30, 40, 50}");
         failed++;
      end

      // Test 4: find with <= operator
      result = q.find with (item <= 30);
      $display("Test 4: find (item <= 30): size=%0d", result.size());
      foreach(result[i]) $display("  result[%0d] = %0d", i, result[i]);
      if (result.size() == 3 && result[0] == 10 && result[1] == 20 && result[2] == 30) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {10, 20, 30}");
         failed++;
      end

      // Test 5: find with != operator
      result = q.find with (item != 30);
      $display("Test 5: find (item != 30): size=%0d", result.size());
      foreach(result[i]) $display("  result[%0d] = %0d", i, result[i]);
      if (result.size() == 4 && result[0] == 10 && result[1] == 20 && result[2] == 40 && result[3] == 50) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {10, 20, 40, 50}");
         failed++;
      end

      // Test 6: find_first with > operator
      single = q.find_first with (item > 35);
      $display("Test 6: find_first (item > 35): size=%0d", single.size());
      foreach(single[i]) $display("  single[%0d] = %0d", i, single[i]);
      if (single.size() == 1 && single[0] == 40) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {40}");
         failed++;
      end

      // Test 7: find_last with < operator
      single = q.find_last with (item < 35);
      $display("Test 7: find_last (item < 35): size=%0d", single.size());
      foreach(single[i]) $display("  single[%0d] = %0d", i, single[i]);
      if (single.size() == 1 && single[0] == 30) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {30}");
         failed++;
      end

      // Test 8: value OP item (operand swap)
      result = q.find with (25 < item);
      $display("Test 8: find (25 < item): size=%0d", result.size());
      foreach(result[i]) $display("  result[%0d] = %0d", i, result[i]);
      if (result.size() == 3 && result[0] == 30 && result[1] == 40 && result[2] == 50) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {30, 40, 50}");
         failed++;
      end

      // Summary
      $display("");
      if (failed == 0) begin
         $display("All %0d tests PASSED", passed);
      end else begin
         $display("%0d tests passed, %0d tests FAILED", passed, failed);
      end
   end

endmodule
