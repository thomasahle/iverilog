// Test SVA sequence delays in antecedents
// Patterns like: expr ##n expr |-> prop

module test;
  logic clk, reset;
  logic a, b, c, d;
  logic valid, ready, done;

  // Simple antecedent with fixed delay: a ##1 b |-> c
  property p_seq_delay_antecedent;
    @(posedge clk) disable iff(reset)
    a ##1 b |-> c;
  endproperty : p_seq_delay_antecedent

  // Antecedent with delay and non-overlapping implication
  property p_seq_delay_nov;
    @(posedge clk) disable iff(reset)
    a ##2 b |=> c;
  endproperty : p_seq_delay_nov

  // Range delay in antecedent (without parentheses)
  property p_range_antecedent;
    @(posedge clk) disable iff(reset)
    valid ##[1:3] ready |-> done;
  endproperty : p_range_antecedent

  // Unbounded delay in antecedent (without parentheses)
  property p_unbounded_antecedent;
    @(posedge clk) disable iff(reset)
    valid ##[1:$] ready |-> done;
  endproperty : p_unbounded_antecedent

  // Different delay values
  property p_delay_3;
    @(posedge clk) disable iff(reset)
    a ##3 b |-> c;
  endproperty : p_delay_3

  // Zero delay in range
  property p_zero_range;
    @(posedge clk) disable iff(reset)
    a ##[0:2] b |-> c;
  endproperty : p_zero_range

  // Assertions
  SEQ_DELAY: assert property (p_seq_delay_antecedent);
  SEQ_DELAY_NOV: assert property (p_seq_delay_nov);
  RANGE_ANT: assert property (p_range_antecedent);
  UNBND_ANT: assert property (p_unbounded_antecedent);
  DELAY_3: assert property (p_delay_3);
  ZERO_RANGE: assert property (p_zero_range);

  // Inline assertions with antecedent delays
  INLINE1: assert property (@(posedge clk) a ##1 b |-> c);
  INLINE2: cover property (@(posedge clk) valid ##2 ready |=> done);
  INLINE3: assert property (@(posedge clk) a ##[0:5] b |-> c);

  initial begin
    $display("PASSED - SVA antecedent delay patterns parsed successfully");
    $finish;
  end
endmodule
