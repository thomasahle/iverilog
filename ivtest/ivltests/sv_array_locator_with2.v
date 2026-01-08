// Test multiple array locator methods with 'with' clause parsing
// This test verifies that comparison operators (>, <) work in 'with' clauses
// These methods return a queue, so we assign to queue variables

module test;
   int arr[$];
   int idx[$];

   initial begin
      arr.push_back(10);
      arr.push_back(20);
      arr.push_back(30);
      arr.push_back(40);
      arr.push_back(50);

      // Test find_first_index with 'with' clause (returns queue with 0 or 1 element)
      idx = arr.find_first_index with (item > 25);
      $display("find_first_index with (item > 25): size=%0d, idx[0]=%0d", idx.size(), idx.size() > 0 ? idx[0] : -1);

      // Test find_last_index with 'with' clause
      idx = arr.find_last_index with (item < 35);
      $display("find_last_index with (item < 35): size=%0d, idx[0]=%0d", idx.size(), idx.size() > 0 ? idx[0] : -1);

      // Test find_index with 'with' clause (returns queue of all matching indices)
      idx = arr.find_index with (item == 30);
      $display("find_index with (item == 30): size=%0d, idx[0]=%0d", idx.size(), idx.size() > 0 ? idx[0] : -1);

      // Verify results are correct
      idx = arr.find_first_index with (item > 25);
      if (idx.size() != 1 || idx[0] != 2) begin
         $display("FAILED: find_first_index with (item > 25) wrong");
         $finish;
      end

      $display("PASSED");
      $finish;
   end
endmodule
