// Test mailbox blocking get/put methods
// Similar to semaphore blocking test - verifies proper thread synchronization

module test;
  mailbox mb;
  int received_value;
  bit get_done;
  bit put_done;

  initial begin
    mb = new(1);  // Bounded mailbox with capacity 1
    get_done = 0;
    put_done = 0;
    received_value = 0;

    // Test 1: Blocking get on empty mailbox
    $display("Test 1: Blocking get on empty mailbox");
    fork
      begin
        // This thread tries to get from empty mailbox - should block
        int msg;
        $display("[%0t] Thread A: calling mb.get() on empty mailbox...", $time);
        mb.get(msg);
        $display("[%0t] Thread A: mb.get() returned, msg=%0d", $time, msg);
        received_value = msg;
        get_done = 1;
      end
      begin
        // This thread puts after a delay - should unblock the getter
        #10;
        $display("[%0t] Thread B: putting value 42...", $time);
        mb.put(42);
        $display("[%0t] Thread B: put done", $time);
        put_done = 1;
      end
    join

    if (get_done && put_done && received_value == 42) begin
      $display("Test 1 PASSED: blocking get received correct value");
    end else begin
      $display("Test 1 FAILED: get_done=%0d, put_done=%0d, received=%0d",
               get_done, put_done, received_value);
    end

    // Test 2: Blocking put on full mailbox
    $display("\nTest 2: Blocking put on full bounded mailbox");
    mb.put(100);  // Fill the mailbox (capacity 1)

    get_done = 0;
    put_done = 0;

    fork
      begin
        // This thread tries to put to full mailbox - should block
        $display("[%0t] Thread C: calling mb.put(200) on full mailbox...", $time);
        mb.put(200);
        $display("[%0t] Thread C: mb.put() returned", $time);
        put_done = 1;
      end
      begin
        // This thread gets after a delay - should unblock the putter
        int msg;
        #10;
        $display("[%0t] Thread D: getting value...", $time);
        mb.get(msg);
        $display("[%0t] Thread D: got %0d", $time, msg);
        get_done = 1;
      end
    join

    // Get the second value
    begin
      int msg;
      mb.get(msg);
      $display("Got second value: %0d (expected 200)", msg);
      if (msg == 200 && get_done && put_done) begin
        $display("Test 2 PASSED: blocking put on full mailbox works");
      end else begin
        $display("Test 2 FAILED");
      end
    end

    // Test 3: Non-blocking try_get returns 0 on empty mailbox
    $display("\nTest 3: Non-blocking try_get on empty mailbox");
    begin
      int msg;
      int result;
      result = mb.try_get(msg);
      if (result == 0) begin
        $display("Test 3 PASSED: try_get returned 0 on empty mailbox");
      end else begin
        $display("Test 3 FAILED: try_get returned %0d", result);
      end
    end

    // Test 4: FIFO order for waiting threads
    $display("\nTest 4: FIFO order for multiple waiting get threads");
    begin
      mailbox mb2 = new();  // Unbounded
      int order[3];
      int idx = 0;

      fork
        begin
          int msg;
          $display("[%0t] Thread E: waiting for get...", $time);
          mb2.get(msg);
          $display("[%0t] Thread E: got %0d", $time, msg);
          order[idx++] = msg;
        end
        begin
          int msg;
          $display("[%0t] Thread F: waiting for get...", $time);
          mb2.get(msg);
          $display("[%0t] Thread F: got %0d", $time, msg);
          order[idx++] = msg;
        end
        begin
          #10;
          $display("[%0t] Thread G: putting values...", $time);
          mb2.put(1);
          mb2.put(2);
          $display("[%0t] Thread G: done putting", $time);
        end
      join

      // Threads should receive in FIFO order
      if (order[0] == 1 && order[1] == 2) begin
        $display("Test 4 PASSED: FIFO order maintained");
      end else begin
        $display("Test 4 FAILED: order was %0d, %0d", order[0], order[1]);
      end
    end

    $display("\nAll mailbox blocking tests complete!");
    $finish;
  end
endmodule
