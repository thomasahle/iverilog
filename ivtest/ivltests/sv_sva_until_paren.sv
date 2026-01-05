// Test SVA parenthesized 'until' operator
module sv_sva_until_paren;
   logic clk = 0;
   logic rst = 1;
   logic a = 0;
   logic b = 0;

   always #5 clk = ~clk;

   // Track assertion results
   int pass_count = 0, fail_count = 0;

   // Test parenthesized until: (a until b)
   // This should check that 'a' holds (single-cycle approximation)
   assert property (@(posedge clk) disable iff (!rst)
      $changed(a) |=> ($stable(a) until $changed(b)))
      pass_count++;
      else fail_count++;

   always @(posedge clk) begin
      static int cycle = 0;
      cycle++;

      case (cycle)
         1: rst <= 1;
         2: a <= 1;  // Change a
         3: a <= 1;  // Keep a stable
         4: a <= 1;  // Keep a stable
         5: b <= 1;  // Change b - ends the until
         6: a <= 0;  // Change a again

         10: begin
            $display("Pass: %0d, Fail: %0d", pass_count, fail_count);
            // We expect some passes (when $stable(a) holds)
            if (pass_count > 0)
               $display("PASSED");
            else
               $display("FAILED");
            $finish;
         end
      endcase
   end

endmodule
