// Test array locator method with 'with' clause
// find_last_index returns queue of int (indices)
module test;
   int arr[$];
   int idx[$];  // Return type is queue

   initial begin
      arr.push_back(10);
      arr.push_back(20);
      arr.push_back(30);

      // find_last_index returns queue of matching indices
      idx = arr.find_last_index with (item == 20);

      if (idx.size() != 1) begin
         $display("FAILED: Expected 1 match, got %0d", idx.size());
         $finish;
      end

      if (idx[0] != 1) begin
         $display("FAILED: Expected index 1, got %0d", idx[0]);
         $finish;
      end

      $display("find_last_index with clause: idx[0]=%0d", idx[0]);
      $display("PASSED");
      $finish;
   end
endmodule
