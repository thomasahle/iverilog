// Test semaphore type declaration and methods
module test;
  semaphore sem;
  int result;
  int pass = 1;

  initial begin
    // Test semaphore creation with default count (0)
    sem = new();
    $display("Created semaphore with default count (0)");

    // Test try_get on empty semaphore - should return 0 (fail)
    result = sem.try_get();
    $display("try_get on empty: %0d (expected 0)", result);
    if (result != 0) begin
      $display("ERROR: try_get on empty semaphore should return 0");
      pass = 0;
    end

    // Put some keys
    sem.put(2);
    $display("Put 2 keys");

    // try_get should succeed now
    result = sem.try_get();
    $display("try_get returned: %0d (expected 1)", result);
    if (result != 1) begin
      $display("ERROR: try_get with available key should return 1");
      pass = 0;
    end

    // Now only 1 key left, try_get(2) should fail
    result = sem.try_get(2);
    $display("try_get(2) with 1 key: %0d (expected 0)", result);
    if (result != 0) begin
      $display("ERROR: try_get(2) with only 1 key should return 0");
      pass = 0;
    end

    // Put 2 more keys (now 3 total)
    sem.put(2);
    $display("Put 2 more keys (now 3 total)");

    // try_get(2) should succeed
    result = sem.try_get(2);
    $display("try_get(2) with 3 keys: %0d (expected 1)", result);
    if (result != 1) begin
      $display("ERROR: try_get(2) with 3 keys should return 1");
      pass = 0;
    end

    // Test with explicit initial count
    sem = new(5);
    $display("Created semaphore with initial count 5");

    // Get multiple keys at once (non-blocking, decrements count)
    sem.get(3);
    $display("Got 3 keys at once (2 remaining)");

    // try_get(3) should fail (only 2 remaining)
    result = sem.try_get(3);
    $display("try_get(3) with 2 keys: %0d (expected 0)", result);
    if (result != 0) begin
      $display("ERROR: try_get(3) with only 2 keys should return 0");
      pass = 0;
    end

    // try_get(2) should succeed
    result = sem.try_get(2);
    $display("try_get(2) with 2 keys: %0d (expected 1)", result);
    if (result != 1) begin
      $display("ERROR: try_get(2) with 2 keys should return 1");
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
