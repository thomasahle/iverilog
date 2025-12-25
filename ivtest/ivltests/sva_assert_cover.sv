// Test SVA assert and cover property statements
// IEEE 1800-2012 Section 16.14

module test;
  logic clk, reset, a, b, c;

  // Property for testing
  property p_test;
    @(posedge clk) disable iff(reset)
    a |-> b;
  endproperty : p_test

  // Labeled assert property
  ASSERT_TEST: assert property (p_test);

  // Labeled cover property
  COVER_TEST: cover property (p_test);

  // Inline assert property
  INLINE_ASSERT: assert property (@(posedge clk) a |-> b);

  // Inline cover property  
  INLINE_COVER: cover property (@(posedge clk) disable iff(reset) a |=> c);

  // Multiple assertions
  CHK_A: assert property (@(posedge clk) a);
  CHK_B: assert property (@(posedge clk) b);
  COV_C: cover property (@(posedge clk) c);

  initial begin
    $display("PASSED - SVA assert and cover statements parsed successfully");
    $finish;
  end
endmodule
