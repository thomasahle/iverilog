// Test multiple variable declarations in for loop init
// SystemVerilog allows: for (int i = 0, j = 10; ...; ...)

module test;
  int sum;
  int product;
  int arr[10];

  initial begin
    // Test 1: Two variables with same type
    $display("Test 1: Two int variables");
    sum = 0;
    begin
      int j_val;
      j_val = 9;
      for (int i = 0, j = 9; i < 10; i = i + 1) begin
        sum = sum + i + j;
        j = j - 1;
      end
    end
    // Each iteration: (0+9) + (1+8) + ... + (9+0) = 9*10 = 90
    if (sum !== 90) begin
      $display("FAILED: Test 1 - sum = %0d, expected 90", sum);
      $finish;
    end
    $display("Test 1 PASSED: sum = %0d", sum);

    // Test 2: Variables used as array indices
    $display("Test 2: Variables as array indices");
    for (int i = 0, j = 0; i < 10; i = i + 1) begin
      arr[i] = j;
      j = i * 2;
    end
    // arr[0] = 0, arr[1] = 0, arr[2] = 2, arr[3] = 4, ...
    // Actually arr[i] = (i-1)*2 for i>0, arr[0]=0
    // Let me recalculate: j starts 0, arr[0]=0, j=0*2=0
    // i=1: arr[1]=0, j=1*2=2
    // i=2: arr[2]=2, j=2*2=4
    // etc. So arr[k] = (k-1)*2 for k>=1, arr[0]=0
    if (arr[0] !== 0) begin
      $display("FAILED: Test 2 - arr[0] = %0d, expected 0", arr[0]);
      $finish;
    end
    if (arr[5] !== 8) begin // (5-1)*2 = 8
      $display("FAILED: Test 2 - arr[5] = %0d, expected 8", arr[5]);
      $finish;
    end
    $display("Test 2 PASSED");

    // Test 3: Three variables
    $display("Test 3: Three variables");
    sum = 0;
    for (int a = 0, b = 1, c = 2; a < 5; a = a + 1) begin
      sum = sum + a + b + c;
      b = b + 1;
      c = c + 1;
    end
    // a=0,b=1,c=2: 3; a=1,b=2,c=3: 6; a=2,b=3,c=4: 9; a=3,b=4,c=5: 12; a=4,b=5,c=6: 15
    // Total: 3+6+9+12+15 = 45
    if (sum !== 45) begin
      $display("FAILED: Test 3 - sum = %0d, expected 45", sum);
      $finish;
    end
    $display("Test 3 PASSED: sum = %0d", sum);

    // Test 4: Variables with different initial values
    $display("Test 4: Different initial values");
    product = 1;
    for (int x = 1, y = 10; x <= 3; x = x + 1) begin
      product = product * x * y;
      y = y - 3;
    end
    // x=1,y=10: 10; x=2,y=7: 14; x=3,y=4: 12
    // 1 * 10 = 10, 10 * 2 * 7 = 140, 140 * 3 * 4 = 1680
    if (product !== 1680) begin
      $display("FAILED: Test 4 - product = %0d, expected 1680", product);
      $finish;
    end
    $display("Test 4 PASSED: product = %0d", product);

    // Test 5: Nested loops with multiple variables
    $display("Test 5: Nested loops");
    sum = 0;
    for (int i = 0, imax = 3; i < imax; i = i + 1) begin
      for (int j = 0, jmax = 4; j < jmax; j = j + 1) begin
        sum = sum + 1;
      end
    end
    if (sum !== 12) begin
      $display("FAILED: Test 5 - sum = %0d, expected 12", sum);
      $finish;
    end
    $display("Test 5 PASSED: sum = %0d", sum);

    $display("PASSED");
  end
endmodule
