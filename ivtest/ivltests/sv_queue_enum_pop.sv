// Test pop_front() and pop_back() on queue of enums
// Verifies that queue methods work on queues whose element type is an enum

module test;
  typedef enum {IDLE, READ, WRITE, ERROR} cmd_e;

  cmd_e cmd_queue[$];
  cmd_e result;
  int pass = 1;

  initial begin
    // Push some enum values
    cmd_queue.push_back(READ);
    cmd_queue.push_back(WRITE);
    cmd_queue.push_back(IDLE);

    $display("Queue size after push: %0d", cmd_queue.size());
    if (cmd_queue.size() != 3) pass = 0;

    // Test pop_front on enum queue
    result = cmd_queue.pop_front();
    $display("pop_front() returned: %s (expected READ)", result.name());
    if (result != READ) pass = 0;

    // Test pop_back on enum queue
    result = cmd_queue.pop_back();
    $display("pop_back() returned: %s (expected IDLE)", result.name());
    if (result != IDLE) pass = 0;

    $display("Queue size after pops: %0d (expected 1)", cmd_queue.size());
    if (cmd_queue.size() != 1) pass = 0;

    // Verify remaining element
    result = cmd_queue[0];
    $display("Remaining element: %s (expected WRITE)", result.name());
    if (result != WRITE) pass = 0;

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
