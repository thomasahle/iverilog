// Test $onehot and $onehot0 as standalone constraints
// Without explicit comparison (e.g., just $onehot(value) instead of $onehot(value) == 1)
module test;
  class tx_onehot;
    rand bit [7:0] value;

    // Constraint: exactly one bit set AND value < 8
    constraint c1 { $onehot(value); }
    constraint c2 { value > 0 && value < 8; }
  endclass

  class tx_onehot0;
    rand bit [7:0] value;

    // Constraint: zero or exactly one bit set AND value < 4
    constraint c1 { $onehot0(value); }
    constraint c2 { value < 4; }
  endclass

  initial begin
    tx_onehot t1 = new();
    tx_onehot0 t2 = new();
    int passed = 1;

    $display("Test 1: $onehot(value) && value > 0 && value < 8");
    $display("Valid values: 1, 2, 4");
    repeat(5) begin
      if (t1.randomize()) begin
        $display("  value = %b (%0d)", t1.value, t1.value);
        if (t1.value >= 8 || t1.value == 0) begin
          $display("  FAILED: range violated");
          passed = 0;
        end
        if (!$onehot(t1.value)) begin
          $display("  FAILED: not one-hot");
          passed = 0;
        end
      end else begin
        $display("  Randomization FAILED");
        passed = 0;
      end
    end

    $display("");
    $display("Test 2: $onehot0(value) && value < 4");
    $display("Valid values: 0, 1, 2");
    repeat(5) begin
      if (t2.randomize()) begin
        $display("  value = %b (%0d)", t2.value, t2.value);
        if (t2.value >= 4) begin
          $display("  FAILED: range violated");
          passed = 0;
        end
        if (!$onehot0(t2.value)) begin
          $display("  FAILED: not onehot0");
          passed = 0;
        end
      end else begin
        $display("  Randomization FAILED");
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
