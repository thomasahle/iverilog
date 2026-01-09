// Test that assertions referencing skipped properties don't cause elaboration errors.
// When a property is skipped due to unsupported sequence constructs (like ##N delays),
// assertions that reference it should produce a warning and be ignored, not cause errors.

module test;
  logic clk, a, b;

  // Initialize clock
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // This property will be skipped due to the ##[1:$] unbounded delay
  property prop_with_delay;
    @(posedge clk) a |-> ##[1:$] b;
  endproperty

  // This assertion references the skipped property.
  // With the fix, it should produce a warning and be ignored (not an error).
  assert property(prop_with_delay);

  // Simple property without sequence delays - should work normally
  property simple_prop;
    @(posedge clk) a |-> b;
  endproperty

  // This assertion should work since simple_prop is supported
  assert property(simple_prop);

  // Cover statement referencing skipped property should also be ignored
  cover property(prop_with_delay);

  initial begin
    a = 0;
    b = 0;
    #20;
    a = 1;
    b = 1;
    #20;
    a = 0;
    #20;
    $display("PASSED");
    $finish;
  end
endmodule
