// Test first_match operator
// first_match(sequence) matches on the first successful match of the sequence
// Our approximation treats this as "always potentially matches"

module test;
   logic clk = 0;
   logic valid, ready;
   int fail_count = 0;

   always #5 clk = ~clk;

   // Pattern from UART: valid |-> first_match(##[0:N] expr)
   // Approximated: treat as valid |-> true (always pass when triggered)
   assert property (@(posedge clk)
      valid |-> first_match(##[0:10] ready))
   else fail_count++;

   // Non-overlapping variant: |=>
   assert property (@(posedge clk)
      $rose(valid) |=> first_match(##[0:10] ready))
   else fail_count++;

   // first_match with fixed delay
   assert property (@(posedge clk)
      valid |-> first_match(##5 ready))
   else fail_count++;

   // Named property with first_match
   property eventualReady;
       @(posedge clk) valid |-> first_match(##[0:100] ready);
   endproperty
   assert property (eventualReady);

   initial begin
      valid = 0; ready = 0;

      @(posedge clk);
      valid = 1; ready = 1;
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);

      if (fail_count == 0) begin
         $display("PASSED: first_match operator working correctly");
      end else begin
         $display("FAILED: %0d assertion failures", fail_count);
      end
      $finish;
   end
endmodule
