// Test array locator methods with item.property pattern
class Transaction;
  int id;
  int data;

  function new(int i = 0, int d = 0);
    id = i;
    data = d;
  endfunction
endclass

module test;
  Transaction q[$];
  int result[$];
  Transaction t;

  initial begin
    // Create queue of transactions with various IDs
    t = new(10, 100);
    q.push_back(t);
    t = new(20, 200);
    q.push_back(t);
    t = new(10, 300);  // Same ID as first
    q.push_back(t);
    t = new(30, 400);
    q.push_back(t);
    t = new(10, 500);  // Same ID as first and third
    q.push_back(t);

    // find_index with item.property == value pattern
    result = q.find_index with (item.id == 10);
    if (result.size() != 3) begin
      $display("FAILED: find_index expected 3 results, got %0d", result.size());
      $finish;
    end
    if (result[0] != 0 || result[1] != 2 || result[2] != 4) begin
      $display("FAILED: find_index returned wrong indices: %0d %0d %0d",
               result[0], result[1], result[2]);
      $finish;
    end

    // find_first_index with item.property pattern
    result = q.find_first_index with (item.id == 20);
    if (result.size() != 1 || result[0] != 1) begin
      $display("FAILED: find_first_index expected [1], got size=%0d", result.size());
      $finish;
    end

    // find_last_index with item.property pattern
    result = q.find_last_index with (item.id == 10);
    if (result.size() != 1 || result[0] != 4) begin
      $display("FAILED: find_last_index expected [4], got size=%0d", result.size());
      $finish;
    end

    // Test with no matches
    result = q.find_index with (item.id == 999);
    if (result.size() != 0) begin
      $display("FAILED: find_index with no matches should return empty queue");
      $finish;
    end

    $display("PASSED");
  end
endmodule
