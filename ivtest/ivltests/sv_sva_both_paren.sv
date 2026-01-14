// Test SVA pattern: (antecedent) |=> (consequent) where both are parenthesized
// This pattern is common in AXI4 and other protocol assertions
// Fixed in parse.y by adding explicit rules for (expr) |-> (expr) and (expr) |=> (expr)
module sv_sva_both_paren;
  logic clk, a, b, valid, ready, aresetn;
  int fail_count = 0;

  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
    aresetn = 1;
    valid = 0; ready = 0;
    a = 0; b = 0;
    #15 valid = 1; a = 5; b = 10;
    #10 a = 5; b = 10;  // stable - should pass
    #10 a = 5; b = 11;  // b changed - should fail
    #10 a = 6; b = 11;  // a changed - should fail
    #10 ready = 1;      // condition not met, no check
    #10 valid = 0;
    #20;
    $display("Fail count: %0d", fail_count);
    if (fail_count == 2)
      $display("PASSED");
    else
      $display("FAILED: expected 2 assertion failures, got %0d", fail_count);
    $finish;
  end

  // Non-overlapping implication with both sides parenthesized
  property if_signals_are_stable_nov;
    @(posedge clk) disable iff (!aresetn)
    (valid==1 && ready==0) |=> ($stable(a) && $stable(b));
  endproperty

  // Overlapping implication with both sides parenthesized
  property if_signals_are_stable_ov;
    @(posedge clk) disable iff (!aresetn)
    (valid==1 && ready==0) |-> ($stable(a) && $stable(b));
  endproperty

  assert property (if_signals_are_stable_nov) else begin
    $display("Assertion failed at time %0t: |=> signals not stable", $time);
    fail_count++;
  end

  // Also test the |-> variant (should fail at same times since we're using $stable)
  assert property (if_signals_are_stable_ov) else begin
    // Just log for testing, don't count
  end
endmodule
