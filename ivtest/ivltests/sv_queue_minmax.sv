// Test min, max, sum, product queue methods
module test;
  int q[$];
  int minq[$];
  int maxq[$];
  int sum_result;
  int product_result;
  int pass_count = 0;
  int fail_count = 0;

  task check(string name, int actual, int expected);
    if (actual == expected) begin
      $display("PASS: %s = %0d", name, actual);
      pass_count++;
    end else begin
      $display("FAIL: %s expected %0d, got %0d", name, expected, actual);
      fail_count++;
    end
  endtask

  initial begin
    // Test 1: Basic queue with various values
    q = '{5, 2, 8, 1, 9};
    $display("Test 1: q = '{5, 2, 8, 1, 9}");

    minq = q.min();
    check("min()", minq[0], 1);

    maxq = q.max();
    check("max()", maxq[0], 9);

    sum_result = q.sum();
    check("sum()", sum_result, 25);

    product_result = q.product();
    check("product()", product_result, 720);

    // Test 2: Queue with negative values
    q = '{-3, 5, -7, 2, 0};
    $display("\nTest 2: q = '{-3, 5, -7, 2, 0}");

    minq = q.min();
    check("min()", minq[0], -7);

    maxq = q.max();
    check("max()", maxq[0], 5);

    sum_result = q.sum();
    check("sum()", sum_result, -3);

    product_result = q.product();
    check("product()", product_result, 0);

    // Test 3: Single element queue
    q = '{42};
    $display("\nTest 3: q = '{42}");

    minq = q.min();
    check("min()", minq[0], 42);

    maxq = q.max();
    check("max()", maxq[0], 42);

    sum_result = q.sum();
    check("sum()", sum_result, 42);

    product_result = q.product();
    check("product()", product_result, 42);

    // Test 4: Queue with duplicate min/max
    q = '{3, 1, 4, 1, 5, 9, 2, 6, 5};
    $display("\nTest 4: q = '{3, 1, 4, 1, 5, 9, 2, 6, 5}");

    minq = q.min();
    check("min()", minq[0], 1);

    maxq = q.max();
    check("max()", maxq[0], 9);

    sum_result = q.sum();
    check("sum()", sum_result, 36);

    // Summary
    $display("\n===================");
    if (fail_count == 0)
      $display("PASSED: All %0d tests passed", pass_count);
    else
      $display("FAILED: %0d passed, %0d failed", pass_count, fail_count);
    $display("===================");
  end
endmodule
