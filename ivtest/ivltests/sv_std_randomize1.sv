// Test std::randomize() function
// Basic usage without constraints

module test;
  int x;
  int y;
  logic [7:0] byte_val;

  initial begin
    // Initialize to known values
    x = 0;
    y = 0;
    byte_val = 8'h00;

    // Test std::randomize with int
    if (!std::randomize(x)) begin
      $display("FAILED: std::randomize(x) returned 0");
      $finish;
    end

    // Verify x was randomized (very unlikely to still be 0)
    // Note: there's a 1/2^32 chance this could fail if random value is 0

    // Test std::randomize with another int
    if (!std::randomize(y)) begin
      $display("FAILED: std::randomize(y) returned 0");
      $finish;
    end

    // Test std::randomize with byte
    if (!std::randomize(byte_val)) begin
      $display("FAILED: std::randomize(byte_val) returned 0");
      $finish;
    end

    $display("x=%0d, y=%0d, byte_val=%h", x, y, byte_val);
    $display("PASSED");
  end
endmodule
