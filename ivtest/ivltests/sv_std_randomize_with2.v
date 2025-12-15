// Test std::randomize() with complex inline constraints
// Tests various constraint patterns that are parsed but not enforced

module test;
  int x, y, z;
  logic [7:0] data;
  int arr[4];

  initial begin
    // Test with inside constraint
    if (!std::randomize(x) with { x inside {[1:100]}; }) begin
      $display("FAILED: std::randomize with inside constraint returned 0");
      $finish;
    end

    // Test with multiple variables
    if (!std::randomize(x, y) with { x < y; }) begin
      $display("FAILED: std::randomize with multiple vars returned 0");
      $finish;
    end

    // Test with complex expression constraint
    if (!std::randomize(data) with { data[7:4] != data[3:0]; }) begin
      $display("FAILED: std::randomize with bit-select constraint returned 0");
      $finish;
    end

    // Test with implication constraint
    if (!std::randomize(x, y) with { (x > 50) -> (y < 100); }) begin
      $display("FAILED: std::randomize with implication returned 0");
      $finish;
    end

    // Note: std::randomize(arr) with array types not yet supported

    $display("x=%0d, y=%0d, data=%h", x, y, data);
    $display("PASSED");
  end
endmodule
