// Test array locator methods with comparison operators in 'with' clause
// Tests: find_first_index, find_last_index, find_index with >, <, >=, <=, !=
module test;
  int arr[$];
  int idx_queue[$];
  int result[$];

  initial begin
    arr.push_back(10);
    arr.push_back(20);
    arr.push_back(30);
    arr.push_back(40);
    arr.push_back(50);

    // Test find_first_index with > operator
    // find_first_index returns a queue with 0 or 1 element
    result = arr.find_first_index with (item > 25);
    if (result.size() != 1 || result[0] != 2) begin
      $display("FAILED: find_first_index with (item > 25) returned wrong result");
      $finish;
    end
    $display("find_first_index with (item > 25) = %0d (expected 2)", result[0]);

    // Test find_last_index with < operator
    result = arr.find_last_index with (item < 35);
    if (result.size() != 1 || result[0] != 2) begin
      $display("FAILED: find_last_index with (item < 35) returned wrong result");
      $finish;
    end
    $display("find_last_index with (item < 35) = %0d (expected 2)", result[0]);

    // Test find_first_index with >= operator
    result = arr.find_first_index with (item >= 30);
    if (result.size() != 1 || result[0] != 2) begin
      $display("FAILED: find_first_index with (item >= 30) returned wrong result");
      $finish;
    end
    $display("find_first_index with (item >= 30) = %0d (expected 2)", result[0]);

    // Test find_last_index with <= operator
    result = arr.find_last_index with (item <= 30);
    if (result.size() != 1 || result[0] != 2) begin
      $display("FAILED: find_last_index with (item <= 30) returned wrong result");
      $finish;
    end
    $display("find_last_index with (item <= 30) = %0d (expected 2)", result[0]);

    // Test find_first_index with != operator
    result = arr.find_first_index with (item != 10);
    if (result.size() != 1 || result[0] != 1) begin
      $display("FAILED: find_first_index with (item != 10) returned wrong result");
      $finish;
    end
    $display("find_first_index with (item != 10) = %0d (expected 1)", result[0]);

    // Test find_index (returns all matching indices) with > operator
    idx_queue = arr.find_index with (item > 25);
    if (idx_queue.size() != 3) begin
      $display("FAILED: find_index with (item > 25) returned %0d elements, expected 3", idx_queue.size());
      $finish;
    end
    if (idx_queue[0] != 2 || idx_queue[1] != 3 || idx_queue[2] != 4) begin
      $display("FAILED: find_index with (item > 25) returned wrong indices");
      $finish;
    end
    $display("find_index with (item > 25) = {%0d, %0d, %0d} (expected {2, 3, 4})",
             idx_queue[0], idx_queue[1], idx_queue[2]);

    // Test with value on left side: "25 < item" should work like "item > 25"
    result = arr.find_first_index with (25 < item);
    if (result.size() != 1 || result[0] != 2) begin
      $display("FAILED: find_first_index with (25 < item) returned wrong result");
      $finish;
    end
    $display("find_first_index with (25 < item) = %0d (expected 2)", result[0]);

    $display("PASSED");
    $finish;
  end
endmodule
