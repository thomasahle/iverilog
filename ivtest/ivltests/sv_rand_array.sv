// Test randomization of unpacked array properties
// All elements should be randomized, not just the first one
module test;
  class tx;
    rand bit [7:0] data [4];
    rand bit [7:0] scalar;

    // Constraint on array element
    constraint c1 { data[0] < 50; }
  endclass

  initial begin
    tx t = new();
    int passed = 1;
    int all_zero_count = 0;
    int data0_ge_50 = 0;

    $display("Testing rand array randomization:");

    repeat(10) begin
      if (t.randomize()) begin
        $display("data[0]=%0d, data[1]=%0d, data[2]=%0d, data[3]=%0d, scalar=%0d",
                 t.data[0], t.data[1], t.data[2], t.data[3], t.scalar);

        // Check constraint on data[0]
        if (t.data[0] >= 50) begin
          $display("  FAILED: data[0] constraint violated");
          data0_ge_50++;
          passed = 0;
        end

        // Count how many iterations have all zeros in data[1:3]
        // This would indicate only data[0] is being randomized
        if (t.data[1] == 0 && t.data[2] == 0 && t.data[3] == 0) begin
          all_zero_count++;
        end
      end else begin
        $display("Randomization FAILED");
        passed = 0;
      end
    end

    $display("");
    // If all_zero_count is too high, array elements aren't being randomized
    if (all_zero_count > 2) begin
      $display("FAILED: data[1:3] appear not to be randomized (too many zeros)");
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
