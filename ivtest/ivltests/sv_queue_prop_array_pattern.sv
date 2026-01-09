// Test array pattern assignment to queue class properties
class Container;
  int data[$];

  function new();
    data = {};
  endfunction
endclass

module test;
  Container c;
  int passed = 0;
  int failed = 0;

  initial begin
    c = new();

    // Test 1: Array pattern assignment to queue property
    $display("Test 1: Array pattern assignment c.data = {10, 20, 30}");
    c.data = {10, 20, 30};

    if (c.data.size() == 3 && c.data[0] == 10 && c.data[1] == 20 && c.data[2] == 30) begin
      $display("  PASS: size=%0d, values=%0d, %0d, %0d",
               c.data.size(), c.data[0], c.data[1], c.data[2]);
      passed++;
    end else begin
      $display("  FAIL: size=%0d (expected 3)", c.data.size());
      if (c.data.size() > 0) begin
        foreach(c.data[i])
          $display("    data[%0d] = %0d", i, c.data[i]);
      end
      failed++;
    end

    // Test 2: Clear and re-assign
    $display("Test 2: Clear and re-assign with different values");
    c.data.delete();
    c.data = {100, 200, 300, 400};

    if (c.data.size() == 4 && c.data[0] == 100 && c.data[3] == 400) begin
      $display("  PASS: size=%0d, first=%0d, last=%0d",
               c.data.size(), c.data[0], c.data[3]);
      passed++;
    end else begin
      $display("  FAIL: size=%0d", c.data.size());
      failed++;
    end

    // Test 3: Empty pattern
    $display("Test 3: Empty pattern c.data = {}");
    c.data = {};

    if (c.data.size() == 0) begin
      $display("  PASS: size=%0d", c.data.size());
      passed++;
    end else begin
      $display("  FAIL: size=%0d (expected 0)", c.data.size());
      failed++;
    end

    // Test 4: Array pattern after push_back (mixed mode)
    $display("Test 4: push_back then array pattern");
    c.data.push_back(1);
    c.data.push_back(2);
    c.data = {5, 6, 7, 8, 9};  // Should replace the queue

    if (c.data.size() == 5 && c.data[0] == 5 && c.data[4] == 9) begin
      $display("  PASS: size=%0d", c.data.size());
      passed++;
    end else begin
      $display("  FAIL: size=%0d", c.data.size());
      failed++;
    end

    // Summary
    $display("");
    $display("Results: %0d passed, %0d failed", passed, failed);
    if (failed == 0)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
