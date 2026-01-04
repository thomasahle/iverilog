// Test find_last_index with queue[$].property comparison pattern
// This tests the more complex 'with' clause where the comparison value
// is itself a runtime expression accessing the last element of a queue.

class Transaction;
  int id;
  int prio;

  function new(int id_val, int prio_val);
    id = id_val;
    prio = prio_val;
  endfunction
endclass

module test;
  Transaction txn_queue[$];
  int result[$];

  initial begin
    Transaction t;

    // Create transactions with different IDs and priorities
    t = new(10, 1); txn_queue.push_back(t);  // index 0
    t = new(20, 2); txn_queue.push_back(t);  // index 1
    t = new(10, 3); txn_queue.push_back(t);  // index 2
    t = new(30, 4); txn_queue.push_back(t);  // index 3
    t = new(10, 5); txn_queue.push_back(t);  // index 4 (last, id=10)

    $display("Queue has %0d elements", txn_queue.size());
    $display("Last element id = %0d", txn_queue[$].id);

    // Find all indices where item.id matches the last element's id (10)
    // Should return indices: 0, 2, 4
    result = txn_queue.find_index with (item.id == txn_queue[$].id);

    $display("find_index with item.id == txn_queue[$].id (10):");
    if (result.size() == 3) begin
      $display("  Found %0d indices (expected 3)", result.size());
      if (result[0] == 0 && result[1] == 2 && result[2] == 4)
        $display("  Indices correct: %0d, %0d, %0d", result[0], result[1], result[2]);
      else
        $display("  FAILED: Got indices %0d, %0d, %0d (expected 0, 2, 4)",
                 result[0], result[1], result[2]);
    end else begin
      $display("  FAILED: Got %0d indices (expected 3)", result.size());
    end

    // Find last index where item.id matches the last element's id
    result = txn_queue.find_last_index with (item.id == txn_queue[$].id);

    $display("find_last_index with item.id == txn_queue[$].id:");
    if (result.size() == 1 && result[0] == 4) begin
      $display("  PASSED: Last index is %0d (expected 4)", result[0]);
    end else begin
      $display("  FAILED: result size=%0d, value=%0d (expected size=1, value=4)",
               result.size(), result.size() > 0 ? result[0] : -1);
    end

    // Find first index where item.id matches the last element's id
    result = txn_queue.find_first_index with (item.id == txn_queue[$].id);

    $display("find_first_index with item.id == txn_queue[$].id:");
    if (result.size() == 1 && result[0] == 0) begin
      $display("  PASSED: First index is %0d (expected 0)", result[0]);
    end else begin
      $display("  FAILED: result size=%0d, value=%0d (expected size=1, value=0)",
               result.size(), result.size() > 0 ? result[0] : -1);
    end

    // Test with different last element - change to id=30
    t = new(30, 6); txn_queue.push_back(t);  // index 5 (new last, id=30)

    $display("After adding id=30, last element id = %0d", txn_queue[$].id);

    // Now find indices matching id=30 (should be 3, 5)
    result = txn_queue.find_index with (item.id == txn_queue[$].id);

    $display("find_index with item.id == txn_queue[$].id (30):");
    if (result.size() == 2 && result[0] == 3 && result[1] == 5) begin
      $display("  PASSED: Found indices %0d, %0d (expected 3, 5)", result[0], result[1]);
    end else begin
      $display("  FAILED: Got %0d indices", result.size());
    end

    $display("PASSED");
  end
endmodule
