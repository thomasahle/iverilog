// Test ##N sequence delays in assertions (N > 1)
// Pattern: a ##N b |-> c means "if a was true N cycles ago and b is true now, then c must be true"
module sv_sva_seq_delayN;
   logic clk = 0;
   logic a = 0, b = 0, c = 0;

   always #5 clk = ~clk;

   // Assertion: a ##2 b |-> c
   // Should check: if $past(a,2) && b then c
   assert property (@(posedge clk) a ##2 b |-> c)
      else $display("FAIL: a ##2 b |-> c failed at time %0t", $time);

   // Assertion: a ##3 b |-> c
   assert property (@(posedge clk) a ##3 b |-> c)
      else $display("FAIL: a ##3 b |-> c failed at time %0t", $time);

   // Test sequence: set a, wait 2 cycles, then b with c
   initial begin
      @(negedge clk);
      @(negedge clk);
      @(negedge clk);

      // Test 1: a=1, wait 2 cycles, b=1 with c=1 (should pass ##2 assertion)
      a <= 1; b <= 0; c <= 0;
      @(negedge clk);
      a <= 0; b <= 0; c <= 0;  // 1 cycle after a
      @(negedge clk);
      a <= 0; b <= 1; c <= 1;  // 2 cycles after a - b triggers, c must be true
      @(negedge clk);
      b <= 0; c <= 0;
      @(negedge clk);
      @(negedge clk);

      // Test 2: a=1, wait 3 cycles, b=1 with c=1 (should pass ##3 assertion)
      a <= 1; b <= 0; c <= 0;
      @(negedge clk);
      a <= 0; b <= 0; c <= 0;  // 1 cycle after a
      @(negedge clk);
      a <= 0; b <= 0; c <= 0;  // 2 cycles after a
      @(negedge clk);
      a <= 0; b <= 1; c <= 1;  // 3 cycles after a - b triggers, c must be true
      @(negedge clk);
      b <= 0; c <= 0;
      @(negedge clk);
      @(negedge clk);

      $display("PASSED: ##N sequence delay test completed");
      $finish;
   end
endmodule
