// Test min_index() and max_index() queue methods
// Returns queue of indices where min/max value(s) occur

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
      // Test 1: Queue with single min/max
      q = '{30, 10, 20, 50, 40};

      $display("Test 1: Queue with single min/max");
      $display("  q = '{30, 10, 20, 50, 40}");

      indices = q.min_index();
      $display("  min_index returns: %p", indices);
      check("min_index.size()", indices.size(), 1);
      check("min_index[0]", indices[0], 1);  // Index of 10

      indices = q.max_index();
      $display("  max_index returns: %p", indices);
      check("max_index.size()", indices.size(), 1);
      check("max_index[0]", indices[0], 3);  // Index of 50

      // Test 2: Queue with multiple min values
      q = '{20, 5, 30, 5, 10, 5};

      $display("\nTest 2: Queue with multiple min values");
      $display("  q = '{20, 5, 30, 5, 10, 5}");

      indices = q.min_index();
      $display("  min_index returns: %p", indices);
      check("min_index.size()", indices.size(), 3);  // Three 5s
      check("min_index[0]", indices[0], 1);  // First 5 at index 1
      check("min_index[1]", indices[1], 3);  // Second 5 at index 3
      check("min_index[2]", indices[2], 5);  // Third 5 at index 5

      // Test 3: Queue with multiple max values
      q = '{100, 50, 100, 30, 100};

      $display("\nTest 3: Queue with multiple max values");
      $display("  q = '{100, 50, 100, 30, 100}");

      indices = q.max_index();
      $display("  max_index returns: %p", indices);
      check("max_index.size()", indices.size(), 3);  // Three 100s
      check("max_index[0]", indices[0], 0);  // First 100 at index 0
      check("max_index[1]", indices[1], 2);  // Second 100 at index 2
      check("max_index[2]", indices[2], 4);  // Third 100 at index 4

      // Test 4: Queue with negative numbers
      q = '{-10, 5, -20, 15, -20, 0};

      $display("\nTest 4: Queue with negative numbers");
      $display("  q = '{-10, 5, -20, 15, -20, 0}");

      indices = q.min_index();
      $display("  min_index returns: %p", indices);
      check("min_index.size()", indices.size(), 2);  // Two -20s
      check("min_index[0]", indices[0], 2);  // First -20 at index 2
      check("min_index[1]", indices[1], 4);  // Second -20 at index 4

      indices = q.max_index();
      $display("  max_index returns: %p", indices);
      check("max_index.size()", indices.size(), 1);
      check("max_index[0]", indices[0], 3);  // 15 at index 3

      // Test 5: Empty queue
      q = {};

      $display("\nTest 5: Empty queue");
      $display("  q = '{}");

      indices = q.min_index();
      $display("  min_index returns: %p", indices);
      check("min_index.size()", indices.size(), 0);

      indices = q.max_index();
      $display("  max_index returns: %p", indices);
      check("max_index.size()", indices.size(), 0);

      // Test 6: Single element queue
      q = '{42};

      $display("\nTest 6: Single element queue");
      $display("  q = '{42}");

      indices = q.min_index();
      $display("  min_index returns: %p", indices);
      check("min_index.size()", indices.size(), 1);
      check("min_index[0]", indices[0], 0);

      indices = q.max_index();
      $display("  max_index returns: %p", indices);
      check("max_index.size()", indices.size(), 1);
      check("max_index[0]", indices[0], 0);

      // Test 7: All same values
      q = '{7, 7, 7, 7};

      $display("\nTest 7: All same values");
      $display("  q = '{7, 7, 7, 7}");

      indices = q.min_index();
      $display("  min_index returns: %p", indices);
      check("min_index.size()", indices.size(), 4);

      indices = q.max_index();
      $display("  max_index returns: %p", indices);
      check("max_index.size()", indices.size(), 4);

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
