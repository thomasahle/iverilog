// Test function with output ports (IEEE 1800-2012 13.4.1)
// SystemVerilog allows output and inout ports in functions

module test;

  // Function with output port - returns status, outputs result via parameter
  function bit compute_with_result(input int a, input int b, output int result);
    result = a + b;
    if (result > 100)
      return 1; // overflow
    else
      return 0; // ok
  endfunction

  // Function with multiple output ports
  function void swap_if_needed(input int a, input int b, output int smaller, output int larger);
    if (a < b) begin
      smaller = a;
      larger = b;
    end else begin
      smaller = b;
      larger = a;
    end
  endfunction

  // Function with inout port
  function void increment(inout int value, input int amount);
    value = value + amount;
  endfunction

  int result, x, y;
  bit status;

  initial begin
    // Test output port
    status = compute_with_result(30, 40, result);
    if (result !== 70) begin
      $display("FAILED: compute_with_result - expected 70, got %0d", result);
      $finish;
    end
    if (status !== 0) begin
      $display("FAILED: compute_with_result - expected status 0, got %0d", status);
      $finish;
    end

    // Test overflow case
    status = compute_with_result(50, 60, result);
    if (result !== 110) begin
      $display("FAILED: overflow result - expected 110, got %0d", result);
      $finish;
    end
    if (status !== 1) begin
      $display("FAILED: overflow status - expected 1, got %0d", status);
      $finish;
    end

    // Test multiple output ports
    swap_if_needed(30, 10, x, y);
    if (x !== 10) begin
      $display("FAILED: swap_if_needed smaller - expected 10, got %0d", x);
      $finish;
    end
    if (y !== 30) begin
      $display("FAILED: swap_if_needed larger - expected 30, got %0d", y);
      $finish;
    end

    // Test inout port
    x = 10;
    increment(x, 5);
    if (x !== 15) begin
      $display("FAILED: increment - expected 15, got %0d", x);
      $finish;
    end

    $display("PASSED");
  end
endmodule
