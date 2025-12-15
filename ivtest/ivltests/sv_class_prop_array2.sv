// Test class property arrays with 2D arrays
// Tests that multi-dimensional arrays work correctly

class Matrix;
  int data[3][4];  // 3 rows, 4 columns
  bit [7:0] bytes[2][2];

  function new();
    int i, j;
    for (i = 0; i < 3; i++)
      for (j = 0; j < 4; j++)
        data[i][j] = i * 10 + j;

    bytes[0][0] = 8'hAA;
    bytes[0][1] = 8'hBB;
    bytes[1][0] = 8'hCC;
    bytes[1][1] = 8'hDD;
  endfunction

  function int sum();
    int total = 0;
    int i, j;
    for (i = 0; i < 3; i++)
      for (j = 0; j < 4; j++)
        total = total + data[i][j];
    return total;
  endfunction
endclass

module test;
  Matrix m;
  int i, j;

  initial begin
    m = new();

    // Verify initialization
    for (i = 0; i < 3; i++) begin
      for (j = 0; j < 4; j++) begin
        if (m.data[i][j] !== i * 10 + j) begin
          $display("FAILED: data[%0d][%0d] = %0d, expected %0d", i, j, m.data[i][j], i * 10 + j);
          $finish;
        end
      end
    end

    // Verify bytes
    if (m.bytes[0][0] !== 8'hAA) begin
      $display("FAILED: bytes[0][0] = %h, expected AA", m.bytes[0][0]);
      $finish;
    end
    if (m.bytes[1][1] !== 8'hDD) begin
      $display("FAILED: bytes[1][1] = %h, expected DD", m.bytes[1][1]);
      $finish;
    end

    // Test sum
    // Sum = (0+1+2+3) + (10+11+12+13) + (20+21+22+23) = 6 + 46 + 86 = 138
    if (m.sum() !== 138) begin
      $display("FAILED: sum() = %0d, expected 138", m.sum());
      $finish;
    end

    // Modify and verify
    m.data[1][2] = 999;
    if (m.data[1][2] !== 999) begin
      $display("FAILED: After modify, data[1][2] = %0d, expected 999", m.data[1][2]);
      $finish;
    end

    // Make sure other elements weren't affected
    if (m.data[1][1] !== 11) begin
      $display("FAILED: data[1][1] was corrupted, got %0d", m.data[1][1]);
      $finish;
    end

    $display("PASSED");
  end
endmodule
