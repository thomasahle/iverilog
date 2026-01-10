// Test weighted dist constraint selection
// This test verifies that := and :/ weights affect random selection

module test;
   int x;
   int count_low = 0;
   int count_high = 0;
   int iterations = 100;

   initial begin
      // Test 1: Verify dist with := (weight per value)
      // x dist { 1 := 9, 100 := 1 } means:
      //   - 1 has weight 9
      //   - 100 has weight 1
      // So x should be 1 about 90% of the time

      for (int i = 0; i < iterations; i++) begin
         // Use std::randomize with weighted dist constraint
         if (!std::randomize(x) with { x dist { 1 := 9, 100 := 1 }; }) begin
            $display("FAILED: randomize returned 0");
            $finish;
         end

         if (x == 1)
            count_low++;
         else if (x == 100)
            count_high++;
         else begin
            $display("FAILED: x=%0d is not 1 or 100", x);
            $finish;
         end
      end

      // With weight 9:1, we expect roughly 90% to be 1
      // Allow some variance (at least 60% should be 1 with 100 iterations)
      if (count_low < 60) begin
         $display("FAILED: Expected more values to be 1 (got %0d out of %0d)", count_low, iterations);
         $finish;
      end

      // Both values should appear at least once
      if (count_high == 0) begin
         $display("WARNING: Value 100 never appeared (possible but unlikely)");
         // Don't fail - this is probabilistic
      end

      $display("PASSED");
      $display("Weighted dist constraints work: dist {1 := 9, 100 := 1}: count_1=%0d count_100=%0d (expected ~90:10)", count_low, count_high);
      $finish;
   end

endmodule
