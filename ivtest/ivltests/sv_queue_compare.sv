// Test queue comparison operations in various contexts
// This tests == and != operators on queues

module test;
  int q1[$];
  int q2[$];
  int q3[$];
  int errors = 0;

  initial begin
    // Initialize queues
    q1 = '{1, 2, 3};
    q2 = '{1, 2, 3};
    q3 = '{1, 2, 4};

    // Test 1: Equal queues should compare equal
    if (q1 == q2) begin
      $display("PASS: q1 == q2 (identical queues)");
    end else begin
      $display("FAIL: q1 == q2 should be true");
      errors++;
    end

    // Test 2: Different queues should compare not equal
    if (q1 != q3) begin
      $display("PASS: q1 != q3 (different last element)");
    end else begin
      $display("FAIL: q1 != q3 should be true");
      errors++;
    end

    // Test 3: Same queue variable compared with itself
    if (q1 == q1) begin
      $display("PASS: q1 == q1 (same variable)");
    end else begin
      $display("FAIL: q1 == q1 should be true");
      errors++;
    end

    // Test 4: Empty queues
    begin
      int empty1[$];
      int empty2[$];
      if (empty1 == empty2) begin
        $display("PASS: empty queues compare equal");
      end else begin
        $display("FAIL: empty queues should compare equal");
        errors++;
      end
    end

    // Test 5: Empty vs non-empty
    begin
      int empty[$];
      if (q1 != empty) begin
        $display("PASS: non-empty != empty queue");
      end else begin
        $display("FAIL: non-empty queue should != empty queue");
        errors++;
      end
    end

    // Test 6: Different sizes
    begin
      int short_q[$] = '{1, 2};
      if (q1 != short_q) begin
        $display("PASS: different size queues are not equal");
      end else begin
        $display("FAIL: different size queues should not be equal");
        errors++;
      end
    end

    // Test 7: Queue comparison in if condition
    q2 = q1;  // Make them equal again
    if (q1 == q2) begin
      $display("PASS: queue comparison works in if condition");
    end else begin
      $display("FAIL: queue comparison in if condition failed");
      errors++;
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
