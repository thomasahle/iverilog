// Test randc cyclic randomization
// randc properties should cycle through all values before repeating

module test;
  class tx;
    randc bit [2:0] val;  // 3-bit randc: values 0-7
    rand bit [3:0] other; // Regular rand for comparison
  endclass

  tx t;
  int seen [8];      // Track which values we've seen
  int cycle_count;
  int passed;
  int total_iterations;
  int all_seen;
  int cycle_valid;
  int i;

  initial begin
    t = new();
    cycle_count = 0;
    passed = 1;
    total_iterations = 0;

    // Initialize seen array
    for (i = 0; i < 8; i++) seen[i] = 0;

    // Run multiple cycles to verify cyclic behavior
    // For a 3-bit randc, we should see all 8 values exactly once per cycle
    repeat(24) begin  // 3 complete cycles
      if (!t.randomize()) begin
        $display("FAILED: Randomization failed");
        passed = 0;
      end

      // Track this value
      seen[t.val]++;
      total_iterations++;

      // Check if we've completed a cycle (seen all 8 values)
      all_seen = 1;
      for (i = 0; i < 8; i++) begin
        if (seen[i] == 0) all_seen = 0;
      end

      if (all_seen) begin
        // Verify each value was seen exactly once in this cycle
        cycle_valid = 1;
        for (i = 0; i < 8; i++) begin
          if (seen[i] != 1) begin
            $display("ERROR: Value %0d seen %0d times in cycle %0d (expected 1)",
                     i, seen[i], cycle_count);
            cycle_valid = 0;
          end
        end

        if (cycle_valid) begin
          cycle_count++;
          $display("Cycle %0d completed successfully after %0d iterations",
                   cycle_count, total_iterations);
          // Reset for next cycle
          for (i = 0; i < 8; i++) seen[i] = 0;
          total_iterations = 0;
        end else begin
          passed = 0;
        end
      end
    end

    // Verify we completed at least 2 full cycles
    if (cycle_count < 2) begin
      $display("FAILED: Only completed %0d cycles (expected at least 2)", cycle_count);
      passed = 0;
    end

    if (passed) $display("PASSED");
    else $display("FAILED");
  end
endmodule
