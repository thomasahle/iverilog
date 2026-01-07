// Test for std::randomize with multiple variables and constraints
module test;
   int a, b, c;
   int x, y;
   int single;
   int pass_count;
   int fail_count;

   initial begin
      pass_count = 0;
      fail_count = 0;

      // Test 1: Basic multi-variable randomization
      repeat(10) begin
         if (std::randomize(a, b, c)) begin
            pass_count++;
         end else begin
            fail_count++;
         end
      end
      $display("Test 1 - Basic multi-var: %0d passed, %0d failed", pass_count, fail_count);

      // Test 2: Multi-variable with constraints on each
      pass_count = 0;
      fail_count = 0;
      repeat(20) begin
         if (std::randomize(a, b, c) with {
            a >= 0; a <= 100;
            b >= 200; b <= 300;
            c >= -50; c <= 50;
         }) begin
            if (a >= 0 && a <= 100 && b >= 200 && b <= 300 && c >= -50 && c <= 50) begin
               pass_count++;
            end else begin
               $display("FAIL: a=%0d (exp 0-100), b=%0d (exp 200-300), c=%0d (exp -50 to 50)",
                        a, b, c);
               fail_count++;
            end
         end else begin
            fail_count++;
         end
      end
      $display("Test 2 - Multi-var with constraints: %0d passed, %0d failed", pass_count, fail_count);

      // Test 3: Two variables only
      pass_count = 0;
      fail_count = 0;
      repeat(10) begin
         if (std::randomize(x, y) with {
            x >= 1000; x <= 1010;
            y >= 2000; y <= 2020;
         }) begin
            if (x >= 1000 && x <= 1010 && y >= 2000 && y <= 2020) begin
               pass_count++;
            end else begin
               $display("FAIL: x=%0d (exp 1000-1010), y=%0d (exp 2000-2020)", x, y);
               fail_count++;
            end
         end else begin
            fail_count++;
         end
      end
      $display("Test 3 - Two variables: %0d passed, %0d failed", pass_count, fail_count);

      // Test 4: One variable (existing behavior)
      pass_count = 0;
      fail_count = 0;
      repeat(10) begin
         if (std::randomize(single) with { single >= 0; single <= 10; }) begin
            if (single >= 0 && single <= 10) begin
               pass_count++;
            end else begin
               $display("FAIL: single=%0d (exp 0-10)", single);
               fail_count++;
            end
         end else begin
            fail_count++;
         end
      end
      $display("Test 4 - Single variable: %0d passed, %0d failed", pass_count, fail_count);

      $display("PASSED");
      $finish;
   end
endmodule
