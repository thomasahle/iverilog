// Test foreach with array modification
// This tests that foreach can be used to modify array elements

module test;
  int arr[8];

  initial begin
    int sum;
    int product;

    // Initialize array using foreach
    foreach (arr[i]) begin
      arr[i] = i + 1;  // Values: 1, 2, 3, 4, 5, 6, 7, 8
    end

    // Sum using foreach
    sum = 0;
    foreach (arr[i]) begin
      $display("arr[%0d] = %0d", i, arr[i]);
      sum = sum + arr[i];
    end

    // Expected sum: 1+2+3+4+5+6+7+8 = 36
    if (sum != 36) begin
      $display("FAILED: sum=%0d, expected 36", sum);
      $finish;
    end

    // Double all values using foreach
    foreach (arr[i]) begin
      arr[i] = arr[i] * 2;
    end

    // Verify doubled values
    sum = 0;
    foreach (arr[i]) begin
      sum = sum + arr[i];
    end

    if (sum != 72) begin
      $display("FAILED: doubled sum=%0d, expected 72", sum);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
