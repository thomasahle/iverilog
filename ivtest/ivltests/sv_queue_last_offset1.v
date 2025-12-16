// Test queue $-n syntax (offset from last element)
// $: last element (index = size - 1)
// $-1: second-to-last element (index = size - 2)
// etc.
module test;
   int queue[$];
   int result;

   initial begin
      // Push some values
      queue.push_back(10);
      queue.push_back(20);
      queue.push_back(30);
      queue.push_back(40);
      queue.push_back(50);

      // Test $: last element (50)
      result = queue[$];
      if (result !== 50) begin
         $display("FAILED: queue[$] returned %0d, expected 50", result);
         $finish;
      end

      // Test $-1: second-to-last element (40)
      result = queue[$-1];
      if (result !== 40) begin
         $display("FAILED: queue[$-1] returned %0d, expected 40", result);
         $finish;
      end

      // Test $-2: third-to-last element (30)
      result = queue[$-2];
      if (result !== 30) begin
         $display("FAILED: queue[$-2] returned %0d, expected 30", result);
         $finish;
      end

      // Test $-4: fifth-to-last element (10)
      result = queue[$-4];
      if (result !== 10) begin
         $display("FAILED: queue[$-4] returned %0d, expected 10", result);
         $finish;
      end

      $display("PASSED");
   end
endmodule
