// Test string queue element method calls
// This tests that string methods can be called on queue elements directly
// without needing to assign to a temp variable first.

module test;
   string str_queue[$];
   int total_len;

   initial begin
      str_queue.push_back("hello");
      str_queue.push_back("world");
      str_queue.push_back("test");

      // Test .len() on queue elements
      if (str_queue[0].len() != 5) begin
         $display("FAILED: str_queue[0].len() should be 5, got %0d", str_queue[0].len());
         $finish;
      end

      if (str_queue[1].len() != 5) begin
         $display("FAILED: str_queue[1].len() should be 5, got %0d", str_queue[1].len());
         $finish;
      end

      if (str_queue[2].len() != 4) begin
         $display("FAILED: str_queue[2].len() should be 4, got %0d", str_queue[2].len());
         $finish;
      end

      // Test using .len() in expressions
      total_len = 0;
      foreach (str_queue[i]) begin
         total_len += str_queue[i].len();
      end

      if (total_len != 14) begin
         $display("FAILED: total length should be 14, got %0d", total_len);
         $finish;
      end

      // Test .len() in conditional
      foreach (str_queue[i]) begin
         if (str_queue[i].len() >= 5) begin
            $display("String '%s' has length >= 5", str_queue[i]);
         end else begin
            $display("String '%s' has length < 5", str_queue[i]);
         end
      end

      $display("PASSED");
      $finish;
   end
endmodule
