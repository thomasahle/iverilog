// Test SVA first_match operator
// IEEE 1800-2012 Section 16.9.5

module test;
  logic clk, reset, a, b;

  // first_match with simple expression
  property p_first_match_simple;
    @(posedge clk) disable iff(reset)
    a |-> first_match(b);
  endproperty : p_first_match_simple

  // first_match with delay range
  property p_first_match_range;
    @(posedge clk) disable iff(reset)
    a |-> first_match((##[0:100] b));
  endproperty : p_first_match_range

  // first_match with non-overlapping implication
  property p_first_match_nov;
    @(posedge clk) disable iff(reset)
    a |=> first_match((##[1:50] b));
  endproperty : p_first_match_nov

  initial begin
    $display("PASSED - SVA first_match operator parsed successfully");
    $finish;
  end
endmodule
