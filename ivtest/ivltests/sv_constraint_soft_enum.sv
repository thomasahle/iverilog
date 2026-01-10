// Test soft constraints with enum properties

module test;

  typedef enum logic [1:0] {
    IDLE  = 2'b00,
    READ  = 2'b01,
    WRITE = 2'b10,
    BURST = 2'b11
  } cmd_t;

  class Transaction;
    rand cmd_t cmd;
    rand logic [7:0] data;

    // Soft constraint - prefers WRITE but can be overridden
    constraint c_default {
      soft cmd == WRITE;
    }

    // Hard constraint on data
    constraint c_data {
      data inside {[10:100]};
    }
  endclass

  initial begin
    Transaction t;
    int write_count = 0;
    int other_count = 0;
    int i;

    t = new();

    // Without override, soft constraint should prefer WRITE
    for (i = 0; i < 20; i++) begin
      if (!t.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      // Check enum value is valid
      if (t.cmd > 3) begin
        $display("FAILED: Invalid cmd value %0d", t.cmd);
        $finish;
      end

      // Check data constraint
      if (t.data < 10 || t.data > 100) begin
        $display("FAILED: data %0d outside range [10:100]", t.data);
        $finish;
      end

      if (t.cmd == WRITE) write_count++;
      else other_count++;
    end

    // With soft constraint, should mostly get WRITE
    $display("Without override: WRITE=%0d, other=%0d", write_count, other_count);

    // Now test with inline constraint override
    write_count = 0;
    other_count = 0;

    for (i = 0; i < 20; i++) begin
      // Override soft constraint to require READ
      if (!t.randomize() with { cmd == READ; }) begin
        $display("FAILED: randomize with override returned 0");
        $finish;
      end

      if (t.cmd != READ) begin
        $display("FAILED: Expected READ, got %0d", t.cmd);
        $finish;
      end
    end

    $display("With READ override: All 20 iterations got READ");

    $display("PASSED");
    $finish;
  end

endmodule
