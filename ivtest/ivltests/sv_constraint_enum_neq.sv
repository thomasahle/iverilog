// Test enum != constraint

module test;

  typedef enum logic [1:0] {
    IDLE     = 2'b00,
    READ     = 2'b01,
    WRITE    = 2'b10,
    RESERVED = 2'b11
  } cmd_t;

  class Transaction;
    rand cmd_t cmd;

    // Constraint: cmd cannot be RESERVED
    constraint c_no_reserved {
      cmd != RESERVED;
    }
  endclass

  initial begin
    Transaction t;
    int counts[4];
    int i;

    t = new();

    // Randomize 100 times
    for (i = 0; i < 100; i++) begin
      if (!t.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      // Check value is valid enum
      if (t.cmd > 3) begin
        $display("FAILED: Invalid cmd value %0d", t.cmd);
        $finish;
      end

      // Check value is not RESERVED
      if (t.cmd == RESERVED) begin
        $display("FAILED: Got RESERVED value which should be excluded");
        $finish;
      end

      counts[t.cmd]++;
    end

    // Should only see IDLE, READ, WRITE
    if (counts[3] != 0) begin
      $display("FAILED: RESERVED count = %0d (should be 0)", counts[3]);
      $finish;
    end

    $display("PASSED");
    $finish;
  end

endmodule
