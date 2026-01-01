// Test multi-dimensional dynamic array access (int[][])
module test;
  int arr[][];
  int x;

  initial begin
    // Test 1: Basic allocation
    arr = new[3];
    if (arr.size() !== 3) begin
      $display("FAILED: arr.size() = %0d, expected 3", arr.size());
      $finish;
    end

    // Test 2: Inner array allocation
    arr[0] = new[2];
    arr[1] = new[3];
    arr[2] = new[1];
    if (arr[0].size() !== 2) begin
      $display("FAILED: arr[0].size() = %0d, expected 2", arr[0].size());
      $finish;
    end
    if (arr[1].size() !== 3) begin
      $display("FAILED: arr[1].size() = %0d, expected 3", arr[1].size());
      $finish;
    end
    if (arr[2].size() !== 1) begin
      $display("FAILED: arr[2].size() = %0d, expected 1", arr[2].size());
      $finish;
    end

    // Test 3: Lvalue assignment (arr[i][j] = value)
    arr[0][0] = 100;
    arr[0][1] = 101;
    arr[1][0] = 200;
    arr[1][1] = 201;
    arr[1][2] = 202;
    arr[2][0] = 300;

    // Test 4: Rvalue access (x = arr[i][j])
    if (arr[0][0] !== 100) begin
      $display("FAILED: arr[0][0] = %0d, expected 100", arr[0][0]);
      $finish;
    end
    if (arr[0][1] !== 101) begin
      $display("FAILED: arr[0][1] = %0d, expected 101", arr[0][1]);
      $finish;
    end
    if (arr[1][0] !== 200) begin
      $display("FAILED: arr[1][0] = %0d, expected 200", arr[1][0]);
      $finish;
    end
    if (arr[1][1] !== 201) begin
      $display("FAILED: arr[1][1] = %0d, expected 201", arr[1][1]);
      $finish;
    end
    if (arr[1][2] !== 202) begin
      $display("FAILED: arr[1][2] = %0d, expected 202", arr[1][2]);
      $finish;
    end
    if (arr[2][0] !== 300) begin
      $display("FAILED: arr[2][0] = %0d, expected 300", arr[2][0]);
      $finish;
    end

    // Test 5: Expression using multi-dimensional access
    x = arr[1][1] + arr[2][0];
    if (x !== 501) begin
      $display("FAILED: arr[1][1] + arr[2][0] = %0d, expected 501", x);
      $finish;
    end

    // Test 6: Variable indices in loop
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 2; j++) begin
        x = arr[i][j];
        if (i == 0 && j == 0 && x !== 100) begin
          $display("FAILED: Loop arr[0][0] = %0d, expected 100", x);
          $finish;
        end
      end
    end

    $display("PASSED");
  end
endmodule
