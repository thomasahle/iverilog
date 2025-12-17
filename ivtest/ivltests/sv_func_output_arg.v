// Test function output and ref arguments
// This tests that output and ref arguments in class functions
// properly pass values back to the caller

package test_pkg;
  class converter;
    // Function with output argument
    function int convert_output(input int a, output int b);
      b = a * 2;
      return a + 1;
    endfunction

    // Function with ref argument
    function int convert_ref(input int a, ref int b);
      b = a * 3;
      return a + 2;
    endfunction

    // Function with multiple output arguments
    function int multi_output(input int a, output int b, output int c);
      b = a * 2;
      c = a * 3;
      return a;
    endfunction
  endclass
endpackage

module test;
  import test_pkg::*;

  initial begin
    int x, y, z, result;
    converter c;
    c = new();

    // Test output argument
    x = 10;
    y = 999;
    result = c.convert_output(x, y);
    if (result != 11) begin
      $display("FAILED: convert_output result=%0d expected 11", result);
      $finish;
    end
    if (y != 20) begin
      $display("FAILED: convert_output y=%0d expected 20", y);
      $finish;
    end

    // Test ref argument
    x = 10;
    y = 999;
    result = c.convert_ref(x, y);
    if (result != 12) begin
      $display("FAILED: convert_ref result=%0d expected 12", result);
      $finish;
    end
    if (y != 30) begin
      $display("FAILED: convert_ref y=%0d expected 30", y);
      $finish;
    end

    // Test multiple output arguments
    x = 5;
    y = 999;
    z = 999;
    result = c.multi_output(x, y, z);
    if (result != 5) begin
      $display("FAILED: multi_output result=%0d expected 5", result);
      $finish;
    end
    if (y != 10) begin
      $display("FAILED: multi_output y=%0d expected 10", y);
      $finish;
    end
    if (z != 15) begin
      $display("FAILED: multi_output z=%0d expected 15", z);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
