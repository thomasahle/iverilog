// Test std::randomize() with inline constraints
module test;
  initial begin
    int value;
    int pass_count = 0;
    int fail_count = 0;

    // Test basic std::randomize with comparison constraints
    repeat (50) begin
      if (!std::randomize(value) with { value >= 10; value <= 20; }) begin
        $display("FAIL: std::randomize returned false");
        fail_count++;
        continue;
      end

      if (value >= 10 && value <= 20) begin
        pass_count++;
      end else begin
        $display("FAIL: value=%0d out of range [10:20]", value);
        fail_count++;
      end
    end

    if (fail_count == 0)
      $display("PASSED: All %0d std::randomize constraint checks passed", pass_count);
    else
      $display("FAILED: %0d failures, %0d passes", fail_count, pass_count);
  end
endmodule
