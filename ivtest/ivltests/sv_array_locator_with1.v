// Test array locator method with 'with' clause parsing
// This test verifies that the syntax parses correctly
// Runtime behavior is stubbed - methods return 0/empty
module test;
   int arr[$];
   int idx;

   initial begin
      arr.push_back(10);
      arr.push_back(20);
      arr.push_back(30);

      // Test that find_last_index parses (returns 0 as stub)
      // The 'with' clause syntax should be accepted
      idx = arr.find_last_index with (item == 20);

      // Since runtime is stubbed, idx will be 0
      // Just verify we got here without crash
      $display("find_last_index with clause parsed, idx=%0d", idx);
      $display("PASSED");
      $finish;
   end
endmodule
