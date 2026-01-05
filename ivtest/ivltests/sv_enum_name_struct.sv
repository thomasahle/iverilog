// Test enum.name() method on various types
// Tests that enum method $ivl_enum_method$name works correctly
module test;
  typedef enum logic [1:0] {
    STATE_IDLE   = 2'b00,
    STATE_ACTIVE = 2'b01,
    STATE_DONE   = 2'b10
  } state_e;

  state_e my_state;
  string name_str;

  initial begin
    // Test 1: basic enum.name()
    my_state = STATE_IDLE;
    name_str = my_state.name();
    $display("Test 1: my_state = %s", name_str);
    if (name_str != "STATE_IDLE") begin
      $display("FAILED: Expected STATE_IDLE, got %s", name_str);
      $finish;
    end

    // Test 2: Change state and verify name
    my_state = STATE_ACTIVE;
    name_str = my_state.name();
    $display("Test 2: my_state = %s", name_str);
    if (name_str != "STATE_ACTIVE") begin
      $display("FAILED: Expected STATE_ACTIVE, got %s", name_str);
      $finish;
    end

    // Test 3: Another state
    my_state = STATE_DONE;
    name_str = my_state.name();
    $display("Test 3: my_state = %s", name_str);
    if (name_str != "STATE_DONE") begin
      $display("FAILED: Expected STATE_DONE, got %s", name_str);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
