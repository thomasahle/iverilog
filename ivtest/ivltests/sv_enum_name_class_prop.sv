// Test that enum .name() method works correctly on class properties.
// This tests that values retrieved from the VVP stack (from class property access)
// are correctly converted to VPI vector values for comparison.
module test;
  typedef enum bit [7:0] {
    STATE_A = 8'd10,
    STATE_B = 8'd20,
    STATE_C = 8'd30
  } state_e;

  class container;
    state_e current;
    rand state_e random_state;
    constraint c1 { random_state == STATE_B; }
  endclass

  initial begin
    container c = new();
    state_e local_val;
    int pass = 1;

    // Test 1: Direct assignment works
    local_val = STATE_A;
    if (local_val.name() != "STATE_A") begin
      $display("FAILED: local_val.name() should be 'STATE_A', got '%s'", local_val.name());
      pass = 0;
    end

    // Test 2: Class property direct assignment
    c.current = STATE_C;
    if (c.current.name() != "STATE_C") begin
      $display("FAILED: c.current.name() should be 'STATE_C', got '%s'", c.current.name());
      pass = 0;
    end

    // Test 3: Class property after randomization
    if (c.randomize()) begin
      if (c.random_state != STATE_B) begin
        $display("FAILED: random_state should be STATE_B (20), got %0d", c.random_state);
        pass = 0;
      end
      if (c.random_state.name() != "STATE_B") begin
        $display("FAILED: c.random_state.name() should be 'STATE_B', got '%s'", c.random_state.name());
        pass = 0;
      end
    end else begin
      $display("FAILED: randomize() returned 0");
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
