// Test basic SVA sequence declaration parsing
// IEEE 1800-2012 Section 16.9

module test;
  logic clk, a, b, c;

  // Basic sequence without ports
  sequence s_basic;
    @(posedge clk) a;
  endsequence

  // Sequence with label
  sequence s_labeled;
    @(posedge clk) b;
  endsequence : s_labeled

  // Sequence with expression
  sequence s_expr;
    @(posedge clk) a && b;
  endsequence : s_expr

  // Sequence without clocking (inherits from property)
  sequence s_no_clock;
    a && b && c;
  endsequence : s_no_clock

  initial begin
    $display("PASSED - SVA sequence declarations parsed successfully");
    $finish;
  end
endmodule
