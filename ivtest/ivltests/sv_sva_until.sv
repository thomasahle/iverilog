// Test SVA 'until' operator and sampled value functions in assertions
module sv_sva_until;
   logic clk = 0;
   logic rst = 1;
   logic ws = 0;
   logic sd = 0;

   always #5 clk = ~clk;

   // Track assertion results
   int stable_pass = 0, stable_fail = 0;
   int changed_pass = 0, changed_fail = 0;

   // Test $stable in assertion
   assert property (@(posedge clk) disable iff (!rst) $stable(sd))
      stable_pass++;
      else stable_fail++;

   // Test $changed in assertion
   assert property (@(posedge clk) disable iff (!rst) !$isunknown(ws))
      changed_pass++;
      else changed_fail++;

   always @(posedge clk) begin
      static int cycle = 0;
      cycle++;

      case (cycle)
         1: rst <= 1;
         2: ws <= 1;
         3: sd <= 0;
         4: sd <= 0;
         5: ws <= 0;
         6: sd <= 1;  // Change sd - should cause $stable to fail
         7: ws <= 1;

         10: begin
            $display("$stable: PASS=%0d, FAIL=%0d", stable_pass, stable_fail);
            $display("!$isunknown: PASS=%0d, FAIL=%0d", changed_pass, changed_fail);
            // We expect stable_fail > 0 when sd changes
            if (stable_pass > 0 && changed_pass > 0)
               $display("PASSED");
            else
               $display("FAILED");
            $finish;
         end
      endcase
   end

endmodule
