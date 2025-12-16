// Test multiple array locator methods with 'with' clause parsing
// This test verifies that the syntax parses correctly for all locator methods
// Runtime behavior is stubbed - methods return 0

module test;
   int arr[$];
   int idx;

   initial begin
      arr.push_back(10);
      arr.push_back(20);
      arr.push_back(30);
      arr.push_back(40);
      arr.push_back(50);

      // Test find_first_index with 'with' clause
      idx = arr.find_first_index with (item > 25);
      $display("find_first_index with (item > 25) parsed, idx=%0d", idx);

      // Test find_last_index with 'with' clause
      idx = arr.find_last_index with (item < 35);
      $display("find_last_index with (item < 35) parsed, idx=%0d", idx);

      // Test find_index with 'with' clause
      idx = arr.find_index with (item == 30);
      $display("find_index with (item == 30) parsed, idx=%0d", idx);

      // Since runtime is stubbed, idx will be 0
      // Just verify we got here without crash
      $display("PASSED");
      $finish;
   end
endmodule
