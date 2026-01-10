// Test mailbox type declaration and methods with real message storage
module test;
  mailbox mb;
  int result;
  int msg;
  int pass = 1;

  initial begin
    // Test mailbox creation with default (unbounded)
    mb = new();
    $display("Created mailbox with default (unbounded)");

    // Test num() on empty mailbox
    result = mb.num();
    $display("num() on empty: %0d", result);
    if (result != 0) begin
      $display("ERROR: expected 0");
      pass = 0;
    end

    // Test try_get on empty mailbox (should return 0)
    result = mb.try_get(msg);
    $display("try_get on empty: %0d", result);
    if (result != 0) begin
      $display("ERROR: expected 0 for try_get on empty");
      pass = 0;
    end

    // Test put message
    mb.put(42);
    $display("Put message 42");

    // Check num() after put
    result = mb.num();
    $display("num() after put: %0d", result);
    if (result != 1) begin
      $display("ERROR: expected 1, got %0d", result);
      pass = 0;
    end

    // Test try_put (should succeed since unbounded)
    result = mb.try_put(100);
    $display("try_put(100) returned: %0d", result);
    if (result != 1) begin
      $display("ERROR: expected 1");
      pass = 0;
    end

    // Check num() is now 2
    result = mb.num();
    $display("num() after second put: %0d", result);
    if (result != 2) begin
      $display("ERROR: expected 2, got %0d", result);
      pass = 0;
    end

    // Test get message (should get 42 - FIFO order)
    mb.get(msg);
    $display("Got message: %0d", msg);
    if (msg != 42) begin
      $display("ERROR: expected 42, got %0d", msg);
      pass = 0;
    end

    // Try get second message (100)
    result = mb.try_get(msg);
    $display("try_get returned: %0d, msg: %0d", result, msg);
    if (result != 1 || msg != 100) begin
      $display("ERROR: expected result=1, msg=100");
      pass = 0;
    end

    // Mailbox should now be empty
    result = mb.num();
    $display("num() after gets: %0d", result);
    if (result != 0) begin
      $display("ERROR: expected 0, got %0d", result);
      pass = 0;
    end

    // Test bounded mailbox
    mb = new(2);
    $display("Created mailbox with bound 2");

    // Put two messages
    mb.put(99);
    mb.put(88);
    $display("Put 99 and 88");

    // Test try_put on full bounded mailbox (should fail)
    result = mb.try_put(77);
    $display("try_put(77) on full: %0d", result);
    if (result != 0) begin
      $display("ERROR: expected 0 for try_put on full mailbox");
      pass = 0;
    end

    // Test peek (should see 99 without removing)
    mb.peek(msg);
    $display("Peeked message: %0d", msg);
    if (msg != 99) begin
      $display("ERROR: expected 99, got %0d", msg);
      pass = 0;
    end

    // Test try_peek
    result = mb.try_peek(msg);
    $display("try_peek returned: %0d, msg: %0d", result, msg);
    if (result != 1 || msg != 99) begin
      $display("ERROR: expected result=1, msg=99");
      pass = 0;
    end

    // Verify peek didn't remove the message
    result = mb.num();
    $display("num() after peeks: %0d", result);
    if (result != 2) begin
      $display("ERROR: expected 2 (peek should not remove), got %0d", result);
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
