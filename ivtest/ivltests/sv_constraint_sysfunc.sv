// Test system functions in constraints
// NOTE: This feature is NOT YET IMPLEMENTED
// This test documents the current limitation

class SysFuncConstraint;
  rand bit [7:0] flags;

  // Constraint using $countones - want exactly one bit set
  // Currently parsed but NOT enforced at runtime
  constraint c_onehot { $countones(flags) == 1; }
endclass

module test;
  SysFuncConstraint obj;
  int i;
  int ones_count;
  int success_count;

  initial begin
    obj = new();

    // Test: $countones constraint
    $display("Test: $countones(flags) == 1 constraint");
    $display("NOTE: System functions in constraints are NOT YET enforced");
    $display("");

    success_count = 0;
    for (i = 0; i < 10; i++) begin
      void'(obj.randomize());
      ones_count = $countones(obj.flags);
      if (ones_count == 1)
        success_count++;
    end

    $display("Result: %0d/10 values had exactly one bit set", success_count);

    if (success_count == 10) begin
      $display("PASSED: System function constraint is being enforced!");
    end else begin
      $display("INFO: System function constraints require implementation");
      $display("      The constraint syntax is accepted but not enforced yet.");
      $display("      Random chance would give ~3% success rate for one-hot.");
    end
  end
endmodule
