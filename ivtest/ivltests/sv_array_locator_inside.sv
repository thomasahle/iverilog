// Test array locator methods with 'item inside {...}' pattern
// Tests find_index, find_first_index, find_last_index with set membership

module test;

   int q[$] = '{10, 20, 30, 20, 40, 50, 20, 60};
   int idx[$];
   int single_idx[$];
   int passed = 0;
   int failed = 0;

   initial begin
      // Test 1: find_index with inside - find all indices where element is in {20, 40}
      idx = q.find_index with (item inside {20, 40});
      $display("Test 1: find_index inside {20, 40}: size=%0d", idx.size());
      foreach(idx[i]) $display("  idx[%0d] = %0d", i, idx[i]);
      if (idx.size() == 4 && idx[0] == 1 && idx[1] == 3 && idx[2] == 4 && idx[3] == 6) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {1, 3, 4, 6}");
         failed++;
      end

      // Test 2: find_first_index with inside - find first index where element is in {30, 50}
      single_idx = q.find_first_index with (item inside {30, 50});
      $display("Test 2: find_first_index inside {30, 50}: size=%0d", single_idx.size());
      foreach(single_idx[i]) $display("  single_idx[%0d] = %0d", i, single_idx[i]);
      if (single_idx.size() == 1 && single_idx[0] == 2) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {2}");
         failed++;
      end

      // Test 3: find_last_index with inside - find last index where element is in {20, 30}
      single_idx = q.find_last_index with (item inside {20, 30});
      $display("Test 3: find_last_index inside {20, 30}: size=%0d", single_idx.size());
      foreach(single_idx[i]) $display("  single_idx[%0d] = %0d", i, single_idx[i]);
      if (single_idx.size() == 1 && single_idx[0] == 6) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {6}");
         failed++;
      end

      // Test 4: find_index with inside - value not in queue
      idx = q.find_index with (item inside {100, 200});
      $display("Test 4: find_index inside {100, 200}: size=%0d", idx.size());
      if (idx.size() == 0) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected empty");
         failed++;
      end

      // Test 5: find_index with inside - single value (equivalent to item == value)
      idx = q.find_index with (item inside {10});
      $display("Test 5: find_index inside {10}: size=%0d", idx.size());
      foreach(idx[i]) $display("  idx[%0d] = %0d", i, idx[i]);
      if (idx.size() == 1 && idx[0] == 0) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {0}");
         failed++;
      end

      // Test 6: find_index with inside - three values
      idx = q.find_index with (item inside {10, 50, 60});
      $display("Test 6: find_index inside {10, 50, 60}: size=%0d", idx.size());
      foreach(idx[i]) $display("  idx[%0d] = %0d", i, idx[i]);
      if (idx.size() == 3 && idx[0] == 0 && idx[1] == 5 && idx[2] == 7) begin
         $display("PASS");
         passed++;
      end else begin
         $display("FAIL: expected {0, 5, 7}");
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
