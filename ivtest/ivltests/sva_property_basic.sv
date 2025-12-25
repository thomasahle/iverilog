// Test basic SVA property declaration parsing
// IEEE 1800-2012 Section 16.12

module test;
  logic clk, reset, a, b, c;

  // Basic property without ports
  property p_basic;
    @(posedge clk) a;
  endproperty

  // Property with label
  property p_labeled;
    @(posedge clk) b;
  endproperty : p_labeled

  // Property with disable iff
  property p_disable_iff;
    @(posedge clk) disable iff(reset)
    a && b;
  endproperty : p_disable_iff

  // Property with overlapping implication
  property p_implies_ov;
    @(posedge clk) disable iff(reset)
    a |-> b;
  endproperty : p_implies_ov

  // Property with non-overlapping implication
  property p_implies_nov;
    @(posedge clk) disable iff(reset)
    a |=> b;
  endproperty : p_implies_nov

  initial begin
    $display("PASSED - SVA property declarations parsed successfully");
    $finish;
  end
endmodule
