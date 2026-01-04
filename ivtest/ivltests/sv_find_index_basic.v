// Test basic array locator methods with 'with' clause
module test;
  int q[$];
  int result[$];

  initial begin
    // Initialize queue
    q = '{10, 20, 30, 20, 40, 20};

    // find_index should return all indices where condition is true
    result = q.find_index with (item == 20);
    if (result.size() != 3) begin
      $display("FAILED: find_index expected 3 results, got %0d", result.size());
      $finish;
    end
    if (result[0] != 1 || result[1] != 3 || result[2] != 5) begin
      $display("FAILED: find_index returned wrong indices: %0d %0d %0d",
               result[0], result[1], result[2]);
      $finish;
    end

    // find_first_index should return first matching index
    result = q.find_first_index with (item == 20);
    if (result.size() != 1 || result[0] != 1) begin
      $display("FAILED: find_first_index expected [1], got size=%0d", result.size());
      $finish;
    end

    // find_last_index should return last matching index
    result = q.find_last_index with (item == 20);
    if (result.size() != 1 || result[0] != 5) begin
      $display("FAILED: find_last_index expected [5], got size=%0d", result.size());
      $finish;
    end

    // Test with no matches
    result = q.find_index with (item == 999);
    if (result.size() != 0) begin
      $display("FAILED: find_index with no matches should return empty queue");
      $finish;
    end

    $display("PASSED");
  end
endmodule
