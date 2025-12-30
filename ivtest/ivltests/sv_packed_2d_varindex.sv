// Test multi-dimensional packed array with variable prefix index
// This tests data[i][j] where i is variable
module test;
  bit [3:0][7:0] data;  // 4 rows of 8 bits each
  bit [7:0] temp;
  int j;

  initial begin
    // Initialize data
    data[0] = 8'hAB;
    data[1] = 8'hCD;
    data[2] = 8'hEF;
    data[3] = 8'h12;

    // Test 1: Variable index to get entire word
    for (int i = 0; i < 4; i++) begin
      temp = data[i];
      $display("data[%0d] = %h", i, temp);
    end

    // Test 2: Variable index with bit select (data[i][j] where i varies)
    j = 0;
    for (int i = 0; i < 4; i++) begin
      $display("data[%0d][0] = %b", i, data[i][0]);
    end

    // Test 3: Variable index with part select (data[i][3:0] where i varies)
    for (int i = 0; i < 4; i++) begin
      $display("data[%0d][3:0] = %h", i, data[i][3:0]);
    end

    // Test 4: Both indices variable
    for (int i = 0; i < 4; i++) begin
      for (j = 0; j < 8; j++) begin
        if (data[i][j])
          $display("data[%0d][%0d] = 1", i, j);
      end
    end

    $display("PASSED");
  end
endmodule
