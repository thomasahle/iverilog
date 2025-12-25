// Test SVA sequence delay operators
// IEEE 1800-2012 Section 16.9.1

module test;
  logic clk, reset, a, b, c;

  // Fixed delay after implication
  property p_delay_fixed;
    @(posedge clk) disable iff(reset)
    a |-> ##1 b;
  endproperty : p_delay_fixed

  // Multiple cycle delay
  property p_delay_multi;
    @(posedge clk) disable iff(reset)
    a |-> ##5 b;
  endproperty : p_delay_multi

  // Delay range
  property p_delay_range;
    @(posedge clk) disable iff(reset)
    a |-> ##[1:5] b;
  endproperty : p_delay_range

  // Zero-based delay range
  property p_delay_zero_range;
    @(posedge clk) disable iff(reset)
    a |-> ##[0:10] b;
  endproperty : p_delay_zero_range

  // Delay with non-overlapping implication
  property p_delay_nov;
    @(posedge clk) disable iff(reset)
    a |=> ##2 b;
  endproperty : p_delay_nov

  // Delay range with non-overlapping implication
  property p_delay_range_nov;
    @(posedge clk) disable iff(reset)
    a |=> ##[1:10] b;
  endproperty : p_delay_range_nov

  initial begin
    $display("PASSED - SVA sequence delay operators parsed successfully");
    $finish;
  end
endmodule
