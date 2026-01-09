// Test that enum constant constraints are properly enforced during randomization.
// This tests that constraints like `val == ENUM_CONST` work correctly.
// Before the fix, enum constants in constraints were not resolved to their values.
module test;
  typedef enum bit [7:0] {
    STATE_IDLE   = 8'd0,
    STATE_READY  = 8'd1,
    STATE_RUN    = 8'd2,
    STATE_DONE   = 8'd3
  } state_e;

  class tx;
    rand state_e current_state;
    rand state_e next_state;
    constraint c1 { current_state == STATE_READY; }
    constraint c2 { next_state == STATE_RUN; }
  endclass

  initial begin
    tx t = new();
    int pass = 1;

    // Test multiple randomizations
    repeat(5) begin
      if (t.randomize()) begin
        $display("current_state = %0d (expected 1), next_state = %0d (expected 2)",
                 t.current_state, t.next_state);
        if (t.current_state != STATE_READY) begin
          $display("FAILED: current_state should be STATE_READY (1), got %0d", t.current_state);
          pass = 0;
        end
        if (t.next_state != STATE_RUN) begin
          $display("FAILED: next_state should be STATE_RUN (2), got %0d", t.next_state);
          pass = 0;
        end
      end else begin
        $display("FAILED: randomize() returned 0");
        pass = 0;
      end
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
