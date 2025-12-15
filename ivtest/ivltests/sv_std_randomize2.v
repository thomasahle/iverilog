// Test std::randomize() with different data types
// Tests int, logic vectors, and byte types

module test;
  int a, b, c;
  logic [15:0] d;
  logic [63:0] e;
  byte f;

  initial begin
    // Initialize to known values
    a = 0; b = 0; c = 0;
    d = 0; e = 0; f = 0;

    // Test randomize on different types
    if (!std::randomize(a)) begin
      $display("FAILED: std::randomize(a) returned 0");
      $finish;
    end

    if (!std::randomize(b)) begin
      $display("FAILED: std::randomize(b) returned 0");
      $finish;
    end

    if (!std::randomize(c)) begin
      $display("FAILED: std::randomize(c) returned 0");
      $finish;
    end

    if (!std::randomize(d)) begin
      $display("FAILED: std::randomize(d) returned 0");
      $finish;
    end

    if (!std::randomize(e)) begin
      $display("FAILED: std::randomize(e) returned 0");
      $finish;
    end

    if (!std::randomize(f)) begin
      $display("FAILED: std::randomize(f) returned 0");
      $finish;
    end

    $display("a=%0d, b=%0d, c=%0d", a, b, c);
    $display("d=%h, e=%h, f=%h", d, e, f);

    // Basic sanity check - at least one value should be non-zero
    if (a == 0 && b == 0 && c == 0 && d == 0 && e == 0 && f == 0) begin
      $display("FAILED: All values are zero (extremely unlikely)");
      $finish;
    end

    $display("PASSED");
  end
endmodule
