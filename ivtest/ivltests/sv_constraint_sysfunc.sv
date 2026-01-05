// Test system functions in constraints
// This tests that $countones(flags) == 1 constraint generates one-hot values

class SysFuncConstraint;
  rand bit [7:0] flags;

  // Constraint using $countones - want exactly one bit set (one-hot value)
  constraint c_onehot { $countones(flags) == 1; }
endclass

module test;
  SysFuncConstraint obj;
  int i;
  int pass_count;
  bit is_power2;

  initial begin
    obj = new();

    // Test: $countones constraint should generate one-hot values
    $display("Test: $countones(flags) == 1 constraint");
    $display("Verifying all generated values are one-hot (power of 2):");
    $display("");

    pass_count = 0;
    for (i = 0; i < 10; i++) begin
      void'(obj.randomize());
      // Check if value is power of 2 (one-hot): v != 0 and v & (v-1) == 0
      is_power2 = (obj.flags != 0) && ((obj.flags & (obj.flags - 1)) == 0);
      if (is_power2)
        pass_count++;
      $display("  val=%3d (0x%02h) is_one_hot=%b", obj.flags, obj.flags, is_power2);
    end

    $display("");
    $display("Result: %0d/10 values are one-hot (power of 2)", pass_count);

    if (pass_count == 10) begin
      $display("PASSED: System function constraint is being enforced!");
    end else begin
      $display("FAILED: Only %0d/10 values are one-hot", pass_count);
    end
  end
endmodule
