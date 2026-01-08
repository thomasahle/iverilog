// Test unique_index() queue method
// Returns queue of indices of first occurrence of each unique value

module test;
   int q[$];
   int indices[$];
   int passed = 0;
   int failed = 0;

   task check(string name, int actual, int expected);
      if (actual === expected) begin
         $display("PASS: %s = %0d", name, actual);
         passed++;
      end else begin
         $display("FAIL: %s = %0d, expected %0d", name, actual, expected);
         failed++;
      end
   endtask

   initial begin
      // Test 1: Queue with duplicates
      q = '{10, 20, 10, 30, 20, 10, 40};
      indices = q.unique_index();

      $display("Test 1: Queue with duplicates");
      $display("  q = '{10, 20, 10, 30, 20, 10, 40}");
      $display("  unique_index returns indices: %p", indices);

      // Should return indices of first occurrences: {0, 1, 3, 6}
      // Index 0 -> first 10
      // Index 1 -> first 20
      // Index 3 -> first 30
      // Index 6 -> first 40
      check("indices.size()", indices.size(), 4);
      check("indices[0]", indices[0], 0);  // First 10 at index 0
      check("indices[1]", indices[1], 1);  // First 20 at index 1
      check("indices[2]", indices[2], 3);  // First 30 at index 3
      check("indices[3]", indices[3], 6);  // First 40 at index 6

      // Test 2: Queue with all unique values
      q = '{1, 2, 3, 4, 5};
      indices = q.unique_index();

      $display("\nTest 2: Queue with all unique values");
      $display("  q = '{1, 2, 3, 4, 5}");
      $display("  unique_index returns indices: %p", indices);

      check("indices.size()", indices.size(), 5);
      check("indices[0]", indices[0], 0);
      check("indices[1]", indices[1], 1);
      check("indices[2]", indices[2], 2);
      check("indices[3]", indices[3], 3);
      check("indices[4]", indices[4], 4);

      // Test 3: Queue with all same values
      q = '{7, 7, 7, 7};
      indices = q.unique_index();

      $display("\nTest 3: Queue with all same values");
      $display("  q = '{7, 7, 7, 7}");
      $display("  unique_index returns indices: %p", indices);

      check("indices.size()", indices.size(), 1);
      check("indices[0]", indices[0], 0);  // Only first occurrence

      // Test 4: Empty queue
      q = {};
      indices = q.unique_index();

      $display("\nTest 4: Empty queue");
      $display("  q = '{}");
      $display("  unique_index returns indices: %p", indices);

      check("indices.size()", indices.size(), 0);

      // Test 5: Single element queue
      q = '{42};
      indices = q.unique_index();

      $display("\nTest 5: Single element queue");
      $display("  q = '{42}");
      $display("  unique_index returns indices: %p", indices);

      check("indices.size()", indices.size(), 1);
      check("indices[0]", indices[0], 0);

      // Summary
      $display("\n========================================");
      $display("Results: %0d passed, %0d failed", passed, failed);
      if (failed == 0)
         $display("PASSED");
      else
         $display("FAILED");
      $finish;
   end
endmodule
