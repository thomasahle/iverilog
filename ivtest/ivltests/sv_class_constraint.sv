// Test class-level constraint enforcement
module test;
  class constrained_item;
    rand int value;
    rand int small_val;

    // Simple comparison constraint
    constraint value_c { value >= 0; value <= 100; }

    // Inside constraint (should generate two bounds)
    constraint small_c { small_val inside {[10:20]}; }
  endclass

  initial begin
    constrained_item item;
    int pass_count = 0;
    int fail_count = 0;

    item = new();

    // Test 100 randomizations - all should respect constraints
    repeat (100) begin
      if (!item.randomize()) begin
        $display("FAIL: randomize() returned false");
        fail_count++;
        continue;
      end

      // Check value constraint: 0 <= value <= 100
      if (item.value < 0 || item.value > 100) begin
        $display("FAIL: value=%0d out of range [0:100]", item.value);
        fail_count++;
      end else begin
        pass_count++;
      end

      // Check small_val constraint: 10 <= small_val <= 20
      if (item.small_val < 10 || item.small_val > 20) begin
        $display("FAIL: small_val=%0d out of range [10:20]", item.small_val);
        fail_count++;
      end else begin
        pass_count++;
      end
    end

    if (fail_count == 0) begin
      $display("PASSED: All %0d constraint checks passed", pass_count);
    end else begin
      $display("FAILED: %0d failures, %0d passes", fail_count, pass_count);
    end
  end
endmodule
