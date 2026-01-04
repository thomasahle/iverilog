// Test array locator methods with 'with' clause on class property queues
class Container;
  int q[$];

  function new();
    // Use push_back instead of array pattern to avoid IVL_EX_ARRAY_PATTERN issue
    q.push_back(10);
    q.push_back(20);
    q.push_back(30);
    q.push_back(20);
    q.push_back(40);
    q.push_back(20);
  endfunction
endclass

module test;
  Container c;
  int result[$];

  initial begin
    c = new();

    // find_index should return all indices where condition is true
    result = c.q.find_index with (item == 20);
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
    result = c.q.find_first_index with (item == 20);
    if (result.size() != 1 || result[0] != 1) begin
      $display("FAILED: find_first_index expected [1], got size=%0d", result.size());
      $finish;
    end

    // find_last_index should return last matching index
    result = c.q.find_last_index with (item == 20);
    if (result.size() != 1 || result[0] != 5) begin
      $display("FAILED: find_last_index expected [5], got size=%0d", result.size());
      $finish;
    end

    // Test with no matches
    result = c.q.find_index with (item == 999);
    if (result.size() != 0) begin
      $display("FAILED: find_index with no matches should return empty queue");
      $finish;
    end

    $display("PASSED");
  end
endmodule
