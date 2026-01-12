// Test semaphore blocking behavior
// - get() should block when count < n
// - put() should wake waiting threads in FIFO order

module test;
  semaphore sem;
  int order[$];  // Track thread completion order
  int result;

  initial begin
    sem = new(0);  // Start with 0 keys

    // Spawn three threads that will try to get keys
    fork
      begin
        // Thread 1 - needs 1 key
        #1;  // Small delay to ensure ordering
        sem.get(1);
        order.push_back(1);
      end
      begin
        // Thread 2 - needs 1 key
        #2;  // Slightly later
        sem.get(1);
        order.push_back(2);
      end
      begin
        // Thread 3 - needs 1 key
        #3;  // Even later
        sem.get(1);
        order.push_back(3);
      end
    join_none

    // Wait for threads to start and block
    #10;

    // At this point, no threads should have completed
    if (order.size() != 0) begin
      $display("FAILED: Expected no completions, got %0d", order.size());
      $finish;
    end

    // Put 1 key - should wake thread 1
    sem.put(1);
    #1;

    if (order.size() != 1 || order[0] != 1) begin
      $display("FAILED: After first put, expected [1], got %p", order);
      $finish;
    end

    // Put 1 key - should wake thread 2
    sem.put(1);
    #1;

    if (order.size() != 2 || order[1] != 2) begin
      $display("FAILED: After second put, expected [1,2], got %p", order);
      $finish;
    end

    // Put 1 key - should wake thread 3
    sem.put(1);
    #1;

    if (order.size() != 3 || order[2] != 3) begin
      $display("FAILED: After third put, expected [1,2,3], got %p", order);
      $finish;
    end

    $display("PASSED");
    $finish;
  end

  // Timeout
  initial begin
    #1000;
    $display("FAILED: Timeout - threads did not wake up");
    $finish;
  end
endmodule
