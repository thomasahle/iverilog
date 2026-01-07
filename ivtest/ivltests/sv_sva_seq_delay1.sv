// Test ##1 sequence delay in assertions
// Pattern: a ##1 b |-> c  means "if a was true and one cycle later b is true, then c must be true"
module sv_sva_seq_delay1;
   logic clk = 0;
   logic a = 0, b = 0, c = 0;
   int pass_count = 0;
   int fail_count = 0;

   always #5 clk = ~clk;

   // Assertion: a ##1 b |-> c
   // Should check: if $past(a) && b then c
   assert property (@(posedge clk) a ##1 b |-> c)
      else $display("FAIL: a ##1 b |-> c failed at time %0t", $time);

   // Test sequence: set a, then b next cycle, check c is required
   initial begin
      @(negedge clk);

      // Test 1: a=1 followed by b=1 with c=1 (should pass)
      a <= 1; b <= 0; c <= 0;
      @(negedge clk);
      a <= 0; b <= 1; c <= 1;  // c must be 1 when a_past && b
      @(negedge clk);
      b <= 0; c <= 0;
      @(negedge clk);
      @(negedge clk);

      // Test 2: a=1 but b=0 next cycle (antecedent fails, no check)
      a <= 1; b <= 0; c <= 0;
      @(negedge clk);
      a <= 0; b <= 0; c <= 0;  // b=0, so sequence doesn't match
      @(negedge clk);
      @(negedge clk);

      // Test 3: Neither a nor b (no assertion triggered)
      a <= 0; b <= 0; c <= 0;
      @(negedge clk);
      @(negedge clk);
      @(negedge clk);

      $display("PASSED: ##1 sequence delay test completed");
      $finish;
   end
endmodule
