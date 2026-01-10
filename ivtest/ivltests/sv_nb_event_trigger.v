// Test non-blocking event trigger ->>
// The ->> operator schedules an event to occur later in the time slot
// Unlike -> which triggers immediately, ->> schedules the trigger

module test;
  event e1, e2;
  int count = 0;
  int errors = 0;

  // Test 1: Basic non-blocking trigger
  initial begin
    fork
      begin
        #10;
        ->> e1;  // Non-blocking trigger - schedules the event
        count = count + 1;
        $display("After ->> e1, count=%0d", count);
      end
      begin
        @(e1);
        count = count + 10;
        $display("Event e1 received, count=%0d", count);
      end
    join

    if (count != 11) begin
      $display("FAILED Test 1: count=%0d (expected 11)", count);
      errors = errors + 1;
    end

    // Test 2: Non-blocking trigger with explicit delay
    count = 0;
    fork
      begin
        #20;
        #5 ->> e2;  // Trigger after additional 5 time units
        count = count + 1;
        $display("After #5 ->> e2, count=%0d", count);
      end
      begin
        @(e2);
        count = count + 100;
        $display("Event e2 received, count=%0d", count);
      end
    join

    if (count != 101) begin
      $display("FAILED Test 2: count=%0d (expected 101)", count);
      errors = errors + 1;
    end

    #1;
    if (errors == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d errors", errors);
    end
  end
endmodule
