// Test that fork branches execute in FIFO (source) order, not LIFO order.
// Each branch records its index, and we verify they ran in order 1, 2, 3.

module test;
  int order[$];

  initial begin
    fork
      begin
        order.push_back(1);
      end
      begin
        order.push_back(2);
      end
      begin
        order.push_back(3);
      end
    join

    // Verify FIFO order: branches should execute in source order
    if (order.size() == 3 && order[0] == 1 && order[1] == 2 && order[2] == 3) begin
      $display("PASSED: Fork branches executed in FIFO order: %0d, %0d, %0d",
               order[0], order[1], order[2]);
    end else begin
      $display("FAILED: Fork branches executed in wrong order: %p", order);
    end

    $finish;
  end
endmodule
