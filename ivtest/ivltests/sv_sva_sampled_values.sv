// Test sampled value functions: $stable, $changed, $rose, $fell, $past
module sv_sva_sampled_values;
   logic clk = 0;
   logic [7:0] data = 8'h00;
   logic flag = 0;
   int pass_count = 0;
   int fail_count = 0;

   // Store results in registers so each function is called only once per cycle
   logic stable_result, changed_result, rose_result, fell_result;
   logic [7:0] past_result;

   always #5 clk = ~clk;

   // Sample all functions at posedge
   always @(posedge clk) begin
      stable_result <= $stable(data);
      changed_result <= $changed(data);
      rose_result <= $rose(flag);
      fell_result <= $fell(flag);
      past_result <= $past(data);
   end

   // Check results
   always @(posedge clk) begin
      static int cycle = 0;
      cycle++;

      case (cycle)
         2: begin
            // Cycle 2 sees results from cycle 1
            // First sample - $stable should be true, $changed false
            $display("Cycle 2: data=%h, $stable=%b, $changed=%b", data, stable_result, changed_result);
            if (stable_result) pass_count++; else fail_count++;
            if (!changed_result) pass_count++; else fail_count++;
         end
         3: begin
            // Cycle 3 sees results from cycle 2 - data still 00, stable
            $display("Cycle 3: data=%h, $stable=%b, $changed=%b", data, stable_result, changed_result);
            if (stable_result) pass_count++; else fail_count++;
            if (!changed_result) pass_count++; else fail_count++;
         end
         4: begin
            // Cycle 4 sees results from cycle 3 - data changed to 42
            $display("Cycle 4: data=%h, $stable=%b, $changed=%b", data, stable_result, changed_result);
            if (!stable_result) pass_count++; else fail_count++;
            if (changed_result) pass_count++; else fail_count++;
         end
         5: begin
            // Cycle 5 sees results from cycle 4 - data stable at 42
            $display("Cycle 5: data=%h, $stable=%b, $changed=%b", data, stable_result, changed_result);
            if (stable_result) pass_count++; else fail_count++;
            if (!changed_result) pass_count++; else fail_count++;
         end

         // Test $rose and $fell
         6: begin
            // Cycle 6 sees results from cycle 5 - flag rose to 1
            $display("Cycle 6: flag=%b, $rose=%b, $fell=%b", flag, rose_result, fell_result);
            if (rose_result) pass_count++; else fail_count++;
            if (!fell_result) pass_count++; else fail_count++;
         end
         7: begin
            // Cycle 7 sees results from cycle 6 - flag stayed at 1
            $display("Cycle 7: flag=%b, $rose=%b, $fell=%b", flag, rose_result, fell_result);
            if (!rose_result) pass_count++; else fail_count++;
            if (!fell_result) pass_count++; else fail_count++;
         end
         8: begin
            // Cycle 8 sees results from cycle 7 - flag fell to 0
            $display("Cycle 8: flag=%b, $rose=%b, $fell=%b", flag, rose_result, fell_result);
            if (!rose_result) pass_count++; else fail_count++;
            if (fell_result) pass_count++; else fail_count++;
         end

         // Test $past - note: past_result has 2-cycle delay (1 from $past + 1 from NBA)
         // So past_result in cycle N shows value from cycle N-2
         // Cycle 9: past_result is from cycle 8 $past which returns cycle 7 value (42)
         // Cycle 10: past_result is from cycle 9 $past which returns cycle 8 value (55)
         // Cycle 11: past_result is from cycle 10 $past which returns cycle 9 value (AA)
         9: begin
            // past_result shows value from cycle 7 (before change to 55)
            $display("Cycle 9: past_result=%h (expect 42)", past_result);
            if (past_result == 8'h42) pass_count++; else fail_count++;
         end
         10: begin
            // past_result shows value from cycle 8 (when data was 55)
            $display("Cycle 10: past_result=%h (expect 55)", past_result);
            if (past_result == 8'h55) pass_count++; else fail_count++;
         end

         11: begin
            $display("PASSED: %0d, FAILED: %0d", pass_count, fail_count);
            if (fail_count == 0)
               $display("PASSED");
            else
               $display("FAILED");
            $finish;
         end
      endcase
   end

   // Drive values at negedge to set up for posedge checks
   always @(negedge clk) begin
      static int neg_cycle = 0;
      neg_cycle++;

      case (neg_cycle)
         2: data <= 8'h42;  // Change data before cycle 3 sample
         4: flag <= 1;      // Rise flag before cycle 5 sample
         6: flag <= 0;      // Fall flag before cycle 7 sample
         7: data <= 8'h55;  // Set up for $past test (sampled in cycle 8)
         8: data <= 8'hAA;  // Set up for $past test (sampled in cycle 9)
      endcase
   end

endmodule
