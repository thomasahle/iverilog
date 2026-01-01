// Test queue.size and darray.size without parentheses
module test;
  int queue[$];
  int darray[];

  initial begin
    // Test queue.size without parentheses
    queue.push_back(1);
    queue.push_back(2);
    queue.push_back(3);

    if (queue.size != 3) begin
      $display("FAILED: queue.size should be 3, got %0d", queue.size);
      $finish;
    end

    // Test darray.size without parentheses
    darray = new[5];
    if (darray.size != 5) begin
      $display("FAILED: darray.size should be 5, got %0d", darray.size);
      $finish;
    end

    // Also test with parentheses for comparison
    if (queue.size() != 3 || darray.size() != 5) begin
      $display("FAILED: size() with parentheses mismatch");
      $finish;
    end

    $display("PASSED");
  end
endmodule
