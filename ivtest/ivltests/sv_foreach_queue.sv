// Test foreach loop with queue
module test;
  int q[$] = '{10, 20, 30, 40, 50};
  int sum = 0;
  int errors = 0;

  initial begin
    // Use foreach to sum all elements
    foreach (q[i]) begin
      sum += q[i];
    end

    if (sum != 150) begin
      $display("FAILED: sum is %0d, expected 150", sum);
      errors++;
    end

    // Use foreach to modify elements
    foreach (q[i]) begin
      q[i] = q[i] * 2;
    end

    if (q[0] != 20 || q[4] != 100) begin
      $display("FAILED: modified q[0]=%0d, q[4]=%0d, expected 20, 100", q[0], q[4]);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
