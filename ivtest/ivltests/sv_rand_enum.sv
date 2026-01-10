// Test that rand enum properties are constrained to valid enum values

module test;

  typedef enum logic [1:0] {
    IDLE  = 2'b00,
    BUSY  = 2'b01,
    WAIT  = 2'b10,
    ERROR = 2'b11
  } state_t;

  typedef enum logic [2:0] {
    RED   = 3'd0,
    GREEN = 3'd1,
    BLUE  = 3'd4,  // Non-contiguous values
    WHITE = 3'd7
  } color_t;

  class Transaction;
    rand state_t state;
    rand color_t color;
    rand int value;  // Regular rand property for comparison

    function void display();
      $display("state=%0d (%s), color=%0d (%s), value=%0d",
               state, state.name(), color, color.name(), value);
    endfunction
  endclass

  initial begin
    Transaction t;
    int state_counts[4];
    int color_counts[8];  // Track all possible 3-bit values
    int valid_states = 0;
    int valid_colors = 0;
    int i;

    t = new();

    // Randomize many times and verify all values are valid enum values
    for (i = 0; i < 100; i++) begin
      if (!t.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      // Track state values
      if (t.state >= 0 && t.state <= 3)
        state_counts[t.state]++;
      else begin
        $display("FAILED: Invalid state value %0d", t.state);
        $finish;
      end

      // Track color values
      if (t.color >= 0 && t.color <= 7)
        color_counts[t.color]++;
      else begin
        $display("FAILED: Invalid color value %0d", t.color);
        $finish;
      end
    end

    // Check that all state values are valid (should only see 0, 1, 2, 3)
    // All 4 states are valid enum values
    valid_states = state_counts[0] + state_counts[1] + state_counts[2] + state_counts[3];
    if (valid_states != 100) begin
      $display("FAILED: Expected 100 valid states, got %0d", valid_states);
      $finish;
    end

    // Check that all color values are valid enum values (only 0, 1, 4, 7)
    // Invalid would be 2, 3, 5, 6
    valid_colors = color_counts[0] + color_counts[1] + color_counts[4] + color_counts[7];
    if (valid_colors != 100) begin
      $display("FAILED: Expected 100 valid colors, got %0d", valid_colors);
      $display("Color counts: 0=%0d, 1=%0d, 2=%0d, 3=%0d, 4=%0d, 5=%0d, 6=%0d, 7=%0d",
               color_counts[0], color_counts[1], color_counts[2], color_counts[3],
               color_counts[4], color_counts[5], color_counts[6], color_counts[7]);
      $finish;
    end

    // Verify no invalid color values were generated
    if (color_counts[2] != 0 || color_counts[3] != 0 ||
        color_counts[5] != 0 || color_counts[6] != 0) begin
      $display("FAILED: Invalid color values generated:");
      $display("  2=%0d, 3=%0d, 5=%0d, 6=%0d",
               color_counts[2], color_counts[3], color_counts[5], color_counts[6]);
      $finish;
    end

    // Report distribution
    $display("State distribution: IDLE=%0d, BUSY=%0d, WAIT=%0d, ERROR=%0d",
             state_counts[0], state_counts[1], state_counts[2], state_counts[3]);
    $display("Color distribution: RED=%0d, GREEN=%0d, BLUE=%0d, WHITE=%0d",
             color_counts[0], color_counts[1], color_counts[4], color_counts[7]);

    $display("PASSED");
    $finish;
  end

endmodule
