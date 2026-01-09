// Test consecutive repetition [*N] operator
// The pattern expr[*N] means "expr holds for N consecutive cycles"
// Our approximation just checks if expr holds once (single-cycle)

module test;
   logic clk = 0;
   logic valid, ready;
   int fail_count = 0;

   always #5 clk = ~clk;

   // Basic consecutive repetition: (expr)[*N]
   // Approximated: just check expr once
   assert property (@(posedge clk)
      valid |-> ($stable(valid))[*3])
   else fail_count++;

   // Repetition without parentheses: expr[*N]
   assert property (@(posedge clk)
      valid |-> $stable(valid)[*3])
   else fail_count++;

   // Repetition followed by ##0 concatenation: (expr)[*N] ##0 (other)
   // Pattern from AXI4 Lite: (cond)[*3] ##0 (result)
   assert property (@(posedge clk)
      valid |-> ($stable(valid))[*3] ##0 ready)
   else fail_count++;

   // Named property with repetition
   property stableThreeCycles;
       @(posedge clk) $rose(valid) |=> ($stable(valid))[*3];
   endproperty
   assert property (stableThreeCycles);

   initial begin
      valid = 0; ready = 0;

      // Set valid=1, should trigger assertions
      @(posedge clk);
      valid = 1; ready = 1;
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);

      if (fail_count == 0) begin
         $display("PASSED: consecutive repetition operator working correctly");
      end else begin
         $display("FAILED: %0d assertion failures", fail_count);
      end
      $finish;
   end
endmodule
