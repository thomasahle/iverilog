// Test for inline constraints with external scope variables
// This tests the pattern: randomize() with { prop >= localVar; }

module test;
   int data;
   int result;

   initial begin
      int local_min;
      int local_max;
      int pass_count;
      int fail_count;

      local_min = 10;
      local_max = 50;
      pass_count = 0;
      fail_count = 0;

      // Test 10 randomizations with external variable constraints
      for (int i = 0; i < 10; i++) begin
         result = std::randomize(data) with { data >= local_min; data <= local_max; };
         if (result != 1) begin
            fail_count++;
         end else if (data < local_min || data > local_max) begin
            $display("FAILED: data=%0d not in [%0d:%0d]", data, local_min, local_max);
            fail_count++;
         end else begin
            pass_count++;
         end
      end

      // Change bounds and test again
      local_min = 100;
      local_max = 200;

      for (int i = 0; i < 10; i++) begin
         result = std::randomize(data) with { data >= local_min; data <= local_max; };
         if (result != 1) begin
            fail_count++;
         end else if (data < local_min || data > local_max) begin
            $display("FAILED: data=%0d not in [%0d:%0d]", data, local_min, local_max);
            fail_count++;
         end else begin
            pass_count++;
         end
      end

      if (fail_count == 0)
         $display("PASSED");
      else
         $display("FAILED: %0d failures", fail_count);

      $finish;
   end
endmodule
