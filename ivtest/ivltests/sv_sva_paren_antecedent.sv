// Test parenthesized antecedent in SVA implication
// (expr) |-> prop should work just like expr |-> prop

module test;
  logic clk = 0;
  logic a, b, c;
  int pass_count = 0;

  always #5 clk = ~clk;

  // Test 1: Simple parenthesized antecedent
  property p1;
    @(posedge clk)
    (a) |-> b;
  endproperty

  // Test 2: Parenthesized OR expression in antecedent
  property p2;
    @(posedge clk)
    (a || b) |-> c;
  endproperty

  // Test 3: Parenthesized antecedent with first_match consequent
  property p3;
    @(posedge clk)
    (a || b) |-> first_match(c);
  endproperty

  // Test 4: Parenthesized antecedent with |=>
  property p4;
    @(posedge clk)
    (a && b) |=> c;
  endproperty

  assert property(p1) pass_count++;
  assert property(p2) pass_count++;
  assert property(p3) pass_count++;
  assert property(p4) pass_count++;

  initial begin
    a = 0; b = 0; c = 0;

    // Cycle 1: All antecedents false, all should pass (vacuously)
    @(posedge clk);
    #1;

    // Cycle 2: Set up for p4 check (a && b was true, c should be true)
    a = 1; b = 1; c = 1;
    @(posedge clk);
    #1;

    // Cycle 3: Check passes
    a = 0; b = 0;
    @(posedge clk);
    #1;

    // Check we got some passes
    if (pass_count > 0) begin
      $display("PASSED: Parenthesized antecedent assertions work");
    end else begin
      $display("FAILED: No assertion passes recorded");
    end
    $finish;
  end
endmodule
