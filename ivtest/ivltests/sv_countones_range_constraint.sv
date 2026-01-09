// Test $countones constraint combined with range constraint
// Bug fix: when $countones(x) == 1 is combined with x < N,
// the one-hot value generator should respect the range constraint
module test;
  class tx;
    rand bit [15:0] value;
    
    // Constraint: exactly 1 bit set AND value < 4
    // Only valid values: 1, 2 (powers of 2 less than 4)
    constraint c1 { $countones(value) == 1; }
    constraint c2 { value > 0 && value < 4; }
  endclass
  
  initial begin
    tx t = new();
    int passed = 1;
    
    $display("Testing: $countones(value) == 1 && value > 0 && value < 4");
    $display("Valid values: 1, 2 (one-hot AND < 4)");
    $display("");
    
    repeat(10) begin
      if (t.randomize()) begin
        $display("value = %b (%0d), $countones = %0d", t.value, t.value, $countones(t.value));
        if (t.value >= 4 || t.value == 0) begin
          $display("FAILED: constraint violated");
          passed = 0;
        end
        if ($countones(t.value) != 1) begin
          $display("FAILED: not one-hot");
          passed = 0;
        end
      end else begin
        $display("Randomization FAILED");
        passed = 0;
      end
    end
    
    $display("");
    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
