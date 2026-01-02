// Test shuffle() and reverse() on module-scope queue
module test;
  int data[$];
  int pass = 1;
  int sum_before, sum_after;

  initial begin
    data = '{1, 2, 3, 4, 5};

    // Calculate sum before
    sum_before = 0;
    for (int i = 0; i < data.size(); i++)
      sum_before += data[i];
    $display("Initial: sum=%0d", sum_before);

    // Test reverse
    data.reverse();
    $display("After reverse: first=%0d, last=%0d", data[0], data[4]);
    if (data[0] != 5 || data[4] != 1) begin
      $display("FAILED: reverse didn't work");
      pass = 0;
    end

    // Reverse again
    data.reverse();
    if (data[0] != 1 || data[4] != 5) begin
      $display("FAILED: second reverse didn't restore");
      pass = 0;
    end

    // Test shuffle
    data.shuffle();
    sum_after = 0;
    for (int i = 0; i < data.size(); i++)
      sum_after += data[i];
    $display("After shuffle: sum=%0d", sum_after);
    if (sum_before != sum_after) begin
      $display("FAILED: shuffle changed sum");
      pass = 0;
    end

    if (pass)
      $display("PASSED");
  end
endmodule
