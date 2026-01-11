// Test queue delete(index) method - removes element at specific index
// Pattern used in AXI4 AVIP: qos_queue.delete(queue_index)

module test;
  int q[$];
  int pass;

  initial begin
    pass = 1;
    q = '{10, 20, 30, 40, 50};

    // Delete middle element (index 2 = value 30)
    q.delete(2);
    if (q.size() != 4) begin
      $display("FAIL: after delete(2), size should be 4, got %0d", q.size());
      pass = 0;
    end
    if (q[2] != 40) begin
      $display("FAIL: after delete(2), q[2] should be 40, got %0d", q[2]);
      pass = 0;
    end

    // Delete first element
    q.delete(0);
    if (q[0] != 20) begin
      $display("FAIL: after delete(0), q[0] should be 20, got %0d", q[0]);
      pass = 0;
    end

    // Delete last element using size-1
    q.delete(q.size()-1);
    if (q[$] != 40) begin
      $display("FAIL: after delete last, q[$] should be 40, got %0d", q[$]);
      pass = 0;
    end

    // Verify final contents: should be {20, 40}
    if (q.size() != 2) begin
      $display("FAIL: final size should be 2, got %0d", q.size());
      pass = 0;
    end
    if (q[0] != 20 || q[1] != 40) begin
      $display("FAIL: final contents wrong: q[0]=%0d q[1]=%0d", q[0], q[1]);
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
