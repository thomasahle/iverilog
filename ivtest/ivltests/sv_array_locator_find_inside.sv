// Test array locator find/find_first/find_last methods with 'item inside {...}' pattern
// These return elements (not indices) that match the set membership test

module test;

   int q[$] = '{10, 20, 30, 20, 40, 50, 20, 60};
   int result[$];
   int single[$];
   int passed = 0;
   int failed = 0;

   initial begin
      // Test 1: find with inside - return all elements that are in {20, 40}
      result = q.find with (item inside {20, 40});
      $display("Test 1: find inside {20, 40}: size=%0d", result.size());
      foreach(result[i]) $display("  result[%0d] = %0d", i, result[i]);
      if (result.size() == 4 && result[0] == 20 && result[1] == 20 && result[2] == 40 && result[3] == 20) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {20, 20, 40, 20}");
         failed++;
      end

      // Test 2: find_first with inside - return first element in {30, 50}
      single = q.find_first with (item inside {30, 50});
      $display("Test 2: find_first inside {30, 50}: size=%0d", single.size());
      foreach(single[i]) $display("  single[%0d] = %0d", i, single[i]);
      if (single.size() == 1 && single[0] == 30) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {30}");
         failed++;
      end

      // Test 3: find_last with inside - return last element in {20, 30}
      single = q.find_last with (item inside {20, 30});
      $display("Test 3: find_last inside {20, 30}: size=%0d", single.size());
      foreach(single[i]) $display("  single[%0d] = %0d", i, single[i]);
      if (single.size() == 1 && single[0] == 20) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {20}");
         failed++;
      end

      // Test 4: find with inside - no match
      result = q.find with (item inside {100, 200});
      $display("Test 4: find inside {100, 200}: size=%0d", result.size());
      if (result.size() == 0) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected empty");
         failed++;
      end

      // Test 5: find with inside - single value
      result = q.find with (item inside {10});
      $display("Test 5: find inside {10}: size=%0d", result.size());
      foreach(result[i]) $display("  result[%0d] = %0d", i, result[i]);
      if (result.size() == 1 && result[0] == 10) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {10}");
         failed++;
      end

      // Test 6: find_first with inside - no match returns empty
      single = q.find_first with (item inside {100, 200});
      $display("Test 6: find_first inside {100, 200}: size=%0d", single.size());
      if (single.size() == 0) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected empty");
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
