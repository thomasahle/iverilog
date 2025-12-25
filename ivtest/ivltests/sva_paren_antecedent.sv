// Test SVA parenthesized antecedent sequences
// Patterns like: (expr ##n expr) |-> prop

module test;
  logic clk, reset;
  logic a, b, c, d;
  logic htrans_idle, hselx, htrans_nonseq;

  // Simple parenthesized antecedent
  property p_paren_simple;
    @(posedge clk) disable iff(reset)
    (a ##1 b) |-> c;
  endproperty : p_paren_simple

  // Parenthesized antecedent with non-overlapping
  property p_paren_nov;
    @(posedge clk) disable iff(reset)
    (a ##2 b) |=> c;
  endproperty : p_paren_nov

  // Parenthesized with range delay
  property p_paren_range;
    @(posedge clk) disable iff(reset)
    (a ##[1:3] b) |-> c;
  endproperty : p_paren_range

  // Parenthesized with unbounded delay
  property p_paren_unbounded;
    @(posedge clk) disable iff(reset)
    (a ##[1:$] b) |-> c;
  endproperty : p_paren_unbounded

  // Real-world AHB-style pattern
  property p_ahb_trans;
    @(posedge clk) disable iff(reset)
    ((htrans_idle) ##1 hselx) |-> htrans_nonseq;
  endproperty : p_ahb_trans

  // Nested parentheses in antecedent
  property p_nested_paren;
    @(posedge clk) disable iff(reset)
    ((a) ##1 (b)) |-> c;
  endproperty : p_nested_paren

  // Assertions
  PAREN_SIMPLE: assert property (p_paren_simple);
  PAREN_NOV: assert property (p_paren_nov);
  PAREN_RANGE: assert property (p_paren_range);
  PAREN_UNBND: assert property (p_paren_unbounded);
  AHB_TRANS: assert property (p_ahb_trans);
  NESTED: assert property (p_nested_paren);

  // Inline with parenthesized antecedent
  INLINE1: assert property (@(posedge clk) (a ##1 b) |-> c);
  INLINE2: cover property (@(posedge clk) (a ##[0:2] b) |=> d);

  initial begin
    $display("PASSED - SVA parenthesized antecedent patterns parsed successfully");
    $finish;
  end
endmodule
