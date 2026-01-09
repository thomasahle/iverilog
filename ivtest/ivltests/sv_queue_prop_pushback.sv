// Test queue property methods using push_back for population
class Container;
  int data[$];

  function new();
    data = {};
  endfunction
endclass

module test;
  Container c;
  int indices[$];
  int passed = 0;
  int failed = 0;

  initial begin
    c = new();

    // Use push_back to populate the queue
    c.data.push_back(10);
    c.data.push_back(20);
    c.data.push_back(10);
    c.data.push_back(30);
    c.data.push_back(20);
    c.data.push_back(10);
    c.data.push_back(40);

    $display("Queue populated with push_back: size = %0d", c.data.size());

    // Test 1: unique_index on class property
    indices = c.data.unique_index();
    $display("Test 1: unique_index on c.data = {10, 20, 10, 30, 20, 10, 40}");
    if (indices.size() == 4 && indices[0] == 0 && indices[1] == 1 &&
        indices[2] == 3 && indices[3] == 6) begin
      $display("  PASS: indices = {%0d, %0d, %0d, %0d}",
               indices[0], indices[1], indices[2], indices[3]);
      passed++;
    end else begin
      $display("  FAIL: got %0d indices", indices.size());
      failed++;
    end

    // Reset queue for test 2
    c.data.delete();
    c.data.push_back(30);
    c.data.push_back(10);
    c.data.push_back(20);
    c.data.push_back(10);
    c.data.push_back(40);

    // Test 2: min_index on class property
    indices = c.data.min_index();
    $display("Test 2: min_index on c.data = {30, 10, 20, 10, 40}");
    if (indices.size() == 2 && indices[0] == 1 && indices[1] == 3) begin
      $display("  PASS: indices = {%0d, %0d}", indices[0], indices[1]);
      passed++;
    end else begin
      $display("  FAIL: got %0d indices", indices.size());
      failed++;
    end

    // Reset queue for test 3
    c.data.delete();
    c.data.push_back(30);
    c.data.push_back(50);
    c.data.push_back(20);
    c.data.push_back(50);
    c.data.push_back(40);

    // Test 3: max_index on class property
    indices = c.data.max_index();
    $display("Test 3: max_index on c.data = {30, 50, 20, 50, 40}");
    if (indices.size() == 2 && indices[0] == 1 && indices[1] == 3) begin
      $display("  PASS: indices = {%0d, %0d}", indices[0], indices[1]);
      passed++;
    end else begin
      $display("  FAIL: got %0d indices", indices.size());
      failed++;
    end

    // Test 4: Empty queue
    c.data.delete();
    indices = c.data.unique_index();
    $display("Test 4: unique_index on empty queue");
    if (indices.size() == 0) begin
      $display("  PASS: empty result");
      passed++;
    end else begin
      $display("  FAIL: got %0d indices", indices.size());
      failed++;
    end

    // Test 5: Single element
    c.data.push_back(42);
    indices = c.data.min_index();
    $display("Test 5: min_index on single element {42}");
    if (indices.size() == 1 && indices[0] == 0) begin
      $display("  PASS: indices = {%0d}", indices[0]);
      passed++;
    end else begin
      $display("  FAIL: got %0d indices", indices.size());
      failed++;
    end

    $display("");
    $display("Results: %0d passed, %0d failed", passed, failed);
    if (failed == 0)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
