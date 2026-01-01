// Test queue shuffle() method
// The shuffle method randomizes the order of queue elements

module test;
  int q[$];
  int original_sum;
  int shuffled_sum;
  int i;
  bit different_order;

  initial begin
    // Initialize queue with known values
    for (i = 0; i < 10; i++) begin
      q.push_back(i);
    end

    // Calculate original sum
    original_sum = 0;
    for (i = 0; i < 10; i++) begin
      original_sum += q[i];
    end

    // Shuffle the queue
    q.shuffle();

    // Calculate shuffled sum (should be same as original)
    shuffled_sum = 0;
    for (i = 0; i < 10; i++) begin
      shuffled_sum += q[i];
    end

    // Check that sum is preserved (elements are same, just reordered)
    if (original_sum != shuffled_sum) begin
      $display("FAILED: Sum mismatch after shuffle. Original=%0d, Shuffled=%0d",
               original_sum, shuffled_sum);
      $finish;
    end

    // Check that at least one element is in a different position
    // (statistically very likely with 10 elements)
    different_order = 0;
    for (i = 0; i < 10; i++) begin
      if (q[i] != i) begin
        different_order = 1;
        break;
      end
    end

    if (different_order) begin
      $display("PASSED: Queue shuffled successfully (sum preserved, order changed)");
    end else begin
      // This is very unlikely but possible
      $display("PASSED: Queue shuffle preserved order (statistically unlikely but valid)");
    end

    $finish;
  end
endmodule
