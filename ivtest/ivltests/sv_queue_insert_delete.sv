// Test queue insert and delete methods
module test;
  int q[$];
  int errors = 0;

  initial begin
    // Build initial queue
    q = '{10, 20, 30, 40, 50};

    // Test insert at beginning
    q.insert(0, 5);
    if (q[0] != 5 || q.size() != 6) begin
      $display("FAILED: insert(0,5) - q[0]=%0d, size=%0d", q[0], q.size());
      errors++;
    end

    // Test insert in middle
    q.insert(3, 25);
    if (q[3] != 25 || q.size() != 7) begin
      $display("FAILED: insert(3,25) - q[3]=%0d, size=%0d", q[3], q.size());
      errors++;
    end

    // Test delete from beginning
    q.delete(0);
    if (q[0] != 10 || q.size() != 6) begin
      $display("FAILED: delete(0) - q[0]=%0d, size=%0d", q[0], q.size());
      errors++;
    end

    // Test delete from middle
    q.delete(2);  // removes 25
    if (q.size() != 5) begin
      $display("FAILED: delete(2) - size=%0d", q.size());
      errors++;
    end

    // Test pop_front
    q = '{1, 2, 3};
    void'(q.pop_front());
    if (q[0] != 2 || q.size() != 2) begin
      $display("FAILED: pop_front - q[0]=%0d, size=%0d", q[0], q.size());
      errors++;
    end

    // Test pop_back
    void'(q.pop_back());
    if (q[0] != 2 || q.size() != 1) begin
      $display("FAILED: pop_back - q[0]=%0d, size=%0d", q[0], q.size());
      errors++;
    end

    // Test push_front and push_back
    q = '{};
    q.push_back(10);
    q.push_front(5);
    q.push_back(15);
    if (q[0] != 5 || q[1] != 10 || q[2] != 15) begin
      $display("FAILED: push - q=%p", q);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
