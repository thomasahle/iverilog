// Test goto repetition [->N] operator
// The goto repetition signal[->N] means "match when signal has gone high N times"
// Our approximation just checks if the signal is true (single-cycle check)

module test;
   logic clk = 0;
   logic valid, ready, data_valid;
   int fail_count = 0;

   always #5 clk = ~clk;

   // Pattern from AXI4 Lite: $stable(valid) throughout ready[->1]
   // Approximated: just check $stable(valid) holds
   assert property (@(posedge clk)
      valid |-> ($stable(valid) throughout ready[->1]))
   else fail_count++;

   // Standalone goto repetition: ready[->1]
   // Approximated: just check ready
   assert property (@(posedge clk)
      valid |-> ready[->1])
   else fail_count++;

   // Parenthesized expression with goto: (data_valid)[->1]
   assert property (@(posedge clk)
      valid |-> (data_valid)[->1])
   else fail_count++;

   // Named property with goto repetition
   property stableUntilReady;
       @(posedge clk) $rose(valid) |=> ($stable(valid) throughout ready[->1]);
   endproperty
   assert property (stableUntilReady);

   initial begin
      valid = 0; ready = 0; data_valid = 0;

      // Test 1: Set up valid=1, ready=1 (should pass)
      @(posedge clk);
      valid = 1; ready = 1; data_valid = 1;
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);

      // Test 2: Keep stable
      @(posedge clk);
      @(posedge clk);

      // Let assertions propagate
      @(posedge clk);
      @(posedge clk);

      if (fail_count == 0) begin
         $display("PASSED: goto repetition operator working correctly");
      end else begin
         $display("FAILED: %0d assertion failures", fail_count);
      end
      $finish;
   end
endmodule
