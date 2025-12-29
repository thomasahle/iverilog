// Test queues with enum element types
// Verifies that enum queues can be declared and used

module test;
  int errors = 0;

  typedef enum logic [1:0] {
    STATE_IDLE = 2'b00,
    STATE_RUN  = 2'b01,
    STATE_STOP = 2'b10,
    STATE_DONE = 2'b11
  } state_e;

  // Declare a queue of enums
  state_e state_queue[$];

  initial begin
    // Test 1: Push values to queue
    state_queue.push_back(STATE_IDLE);
    state_queue.push_back(STATE_RUN);
    state_queue.push_back(STATE_STOP);

    if (state_queue.size() != 3) begin
      $display("FAIL: Expected queue size 3, got %0d", state_queue.size());
      errors++;
    end else begin
      $display("PASS: Queue size is correct");
    end

    // Test 2: Access queue elements
    if (state_queue[0] != STATE_IDLE) begin
      $display("FAIL: Expected STATE_IDLE at [0], got %0d", state_queue[0]);
      errors++;
    end else begin
      $display("PASS: Queue element [0] is correct");
    end

    if (state_queue[1] != STATE_RUN) begin
      $display("FAIL: Expected STATE_RUN at [1], got %0d", state_queue[1]);
      errors++;
    end else begin
      $display("PASS: Queue element [1] is correct");
    end

    // Test 3: Pop from queue
    begin
      state_e popped;
      popped = state_queue.pop_front();
      if (popped != STATE_IDLE) begin
        $display("FAIL: pop_front returned %0d, expected STATE_IDLE", popped);
        errors++;
      end else begin
        $display("PASS: pop_front returned correct value");
      end
    end

    if (state_queue.size() != 2) begin
      $display("FAIL: Expected queue size 2 after pop, got %0d", state_queue.size());
      errors++;
    end else begin
      $display("PASS: Queue size after pop is correct");
    end

    // Report results
    $display("");
    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);

    $finish;
  end
endmodule
