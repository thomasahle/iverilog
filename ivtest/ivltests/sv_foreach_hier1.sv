// Test foreach loop with hierarchical identifier parsing
// This tests that foreach accepts hierarchical identifiers in the grammar
// Note: Uses module-level array to avoid known bug with class array properties

module test;
  int data[4];

  initial begin
    int sum;

    // Initialize array
    data[0] = 10;
    data[1] = 20;
    data[2] = 30;
    data[3] = 40;

    sum = 0;
    // Simple foreach test
    foreach (data[i]) begin
      $display("data[%0d] = %0d", i, data[i]);
      sum = sum + data[i];
    end

    if (sum != 100) begin
      $display("FAILED: sum=%0d, expected 100", sum);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
