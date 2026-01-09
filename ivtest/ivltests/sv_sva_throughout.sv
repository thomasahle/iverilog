// Test throughout operator with single-cycle approximation
// The throughout operator checks that an expression holds during a sequence.
// Our approximation just checks that the expression holds at each cycle.

module test;
   logic clk = 0;
   logic valid, ready, enable;
   int pass_count = 0;
   int fail_count = 0;
   parameter MAX_DELAY = 16;

   always #5 clk = ~clk;

   // Basic throughout test: valid throughout ready
   // Approximated to checking !!valid at each clock edge
   assert property (@(posedge clk)
      valid |-> (valid throughout ready))
   else fail_count++;

   // Parenthesized throughout
   assert property (@(posedge clk)
      enable |-> (enable throughout ready))
   else fail_count++;

   // Throughout with sequence delay ##[m:n]
   // This pattern is common in AXI4 Lite: $stable(valid) throughout (##[0:MAX] $rose(ready))
   assert property (@(posedge clk)
      valid |-> ($stable(valid) throughout (##[0:MAX_DELAY] ready)))
   else fail_count++;

   // Named property with throughout (without problematic comparison operators)
   property stableUntilReady;
       @(posedge clk) $rose(valid) |=> ($stable(valid) throughout (##[0:MAX_DELAY] $rose(ready)));
   endproperty
   assert property (stableUntilReady);

   initial begin
      valid = 0; ready = 0; enable = 0;

      // Test 1: valid=1, ready=1 - assertion should pass (valid holds)
      @(posedge clk);
      valid = 1; ready = 1; enable = 1;
      @(posedge clk);
      @(posedge clk);

      // Test 2: valid=0 after antecedent was 0 - no implication triggered
      valid = 0; enable = 0;
      @(posedge clk);
      @(posedge clk);

      // Let any assertion failures propagate
      @(posedge clk);
      @(posedge clk);

      if (fail_count == 0) begin
         $display("PASSED: throughout operator working correctly");
      end else begin
         $display("FAILED: %0d assertion failures", fail_count);
      end
      $finish;
   end
endmodule
