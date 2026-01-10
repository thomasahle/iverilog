// Test that randc enum properties cycle through all valid enum values

module test;

  typedef enum logic [1:0] {
    IDLE  = 2'b00,
    READ  = 2'b01,
    WRITE = 2'b10,
    BURST = 2'b11
  } cmd_t;

  class Transaction;
    randc cmd_t cmd;
  endclass

  initial begin
    Transaction t;
    int cmd_counts[4];
    int cycle_complete;
    int i;

    t = new();

    // With randc, we should see all 4 values before any repeats
    // Test 3 complete cycles
    for (int cycle = 0; cycle < 3; cycle++) begin
      // Reset counts for this cycle
      for (i = 0; i < 4; i++) cmd_counts[i] = 0;

      // Generate 4 values - should see each exactly once
      for (i = 0; i < 4; i++) begin
        if (!t.randomize()) begin
          $display("FAILED: randomize returned 0");
          $finish;
        end

        // Verify the value is valid (0-3)
        if (t.cmd > 3) begin
          $display("FAILED: Invalid cmd value %0d (should be 0-3)", t.cmd);
          $finish;
        end

        cmd_counts[t.cmd]++;
      end

      // Check that each value was generated exactly once
      for (i = 0; i < 4; i++) begin
        if (cmd_counts[i] != 1) begin
          $display("FAILED: Cycle %0d: cmd_counts[%0d] = %0d (expected 1)",
                   cycle, i, cmd_counts[i]);
          $finish;
        end
      end
      $display("Cycle %0d completed successfully", cycle + 1);
    end

    $display("PASSED");
    $finish;
  end

endmodule
