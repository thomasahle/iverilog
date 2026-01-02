// Test shuffle() and reverse() on class property queues
class Container;
  int data[$];

  function void init();
    for (int i = 1; i <= 5; i++)
      data.push_back(i);
  endfunction

  function int sum();
    int s = 0;
    foreach (data[i]) s += data[i];
    return s;
  endfunction
endclass

module test;
  Container c;
  int pass = 1;
  int sum_before, sum_after;

  initial begin
    c = new();
    c.init();

    sum_before = c.sum();
    $display("Initial: sum=%0d, first=%0d, last=%0d", sum_before, c.data[0], c.data[4]);

    // Test reverse on class property queue
    c.data.reverse();
    $display("After reverse: first=%0d, last=%0d", c.data[0], c.data[4]);
    if (c.data[0] != 5 || c.data[4] != 1) begin
      $display("FAILED: reverse didn't work");
      pass = 0;
    end

    // Reverse again to restore order
    c.data.reverse();
    if (c.data[0] != 1 || c.data[4] != 5) begin
      $display("FAILED: second reverse didn't restore order");
      pass = 0;
    end

    // Test shuffle on class property queue
    c.data.shuffle();
    sum_after = c.sum();
    $display("After shuffle: sum=%0d", sum_after);
    if (sum_before != sum_after) begin
      $display("FAILED: shuffle changed sum");
      pass = 0;
    end

    if (pass)
      $display("PASSED");
  end
endmodule
