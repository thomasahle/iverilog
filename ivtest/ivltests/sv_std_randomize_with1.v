// Test std::randomize() with inline constraints
// The constraints are parsed but not enforced in the current implementation

module test;
  int x;
  int y;

  initial begin
    // Initialize to known values
    x = 0;
    y = 0;

    // Test std::randomize with inline constraints
    // Constraints are parsed but not enforced - this is a compile test
    if (!std::randomize(x) with { x > 0; }) begin
      $display("FAILED: std::randomize with constraint returned 0");
      $finish;
    end

    // Test multiple constraints
    if (!std::randomize(y) with {
      y > 0;
      y < 1000;
    }) begin
      $display("FAILED: std::randomize with multiple constraints returned 0");
      $finish;
    end

    $display("x=%0d, y=%0d", x, y);
    $display("PASSED");
  end
endmodule
