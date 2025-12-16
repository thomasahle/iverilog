// Test queue $-n syntax with dynamic queue operations
// Verify that $-n correctly tracks as queue size changes
module test;
   int queue[$];
   int result;
   int expected;

   initial begin
      // Start with 3 elements
      queue.push_back(100);
      queue.push_back(200);
      queue.push_back(300);

      // Test basic $-n access
      if (queue[$] !== 300) begin
         $display("FAILED: queue[$] = %0d, expected 300", queue[$]);
         $finish;
      end
      if (queue[$-1] !== 200) begin
         $display("FAILED: queue[$-1] = %0d, expected 200", queue[$-1]);
         $finish;
      end
      if (queue[$-2] !== 100) begin
         $display("FAILED: queue[$-2] = %0d, expected 100", queue[$-2]);
         $finish;
      end

      // Add more elements and verify $-n still works
      queue.push_back(400);
      queue.push_back(500);
      // Now queue is: 100, 200, 300, 400, 500

      if (queue[$] !== 500) begin
         $display("FAILED after push: queue[$] = %0d, expected 500", queue[$]);
         $finish;
      end
      if (queue[$-1] !== 400) begin
         $display("FAILED after push: queue[$-1] = %0d, expected 400", queue[$-1]);
         $finish;
      end
      if (queue[$-4] !== 100) begin
         $display("FAILED after push: queue[$-4] = %0d, expected 100", queue[$-4]);
         $finish;
      end

      // Test with variable offset
      for (int i = 0; i < 5; i++) begin
         expected = (5 - i) * 100;
         result = queue[$-i];
         if (result !== expected) begin
            $display("FAILED: queue[$-%0d] = %0d, expected %0d", i, result, expected);
            $finish;
         end
      end

      $display("PASSED");
      $finish;
   end
endmodule
