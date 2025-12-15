// Test: ANSI-style function with implicit return type in package scope
// Tests function with empty parentheses but no return type
// Note: Per IEEE 1800, implicit return type defaults to 1-bit logic

package pkg;
  // ANSI-style function with empty parens, no return type (1-bit logic)
  function bar();
    bar = 1'b1;
  endfunction

  // ANSI-style function with parameters, no return type
  // For multi-bit results, must use explicit return type
  function logic [31:0] add(input int a, input int b);
    add = a + b;
  endfunction
endpackage

module test;
  import pkg::*;

  initial begin
    // bar() returns 1-bit value
    if (bar() !== 1'b1) begin
      $display("FAILED: bar() returned %0b, expected 1", bar());
      $finish;
    end
    // add() has explicit 32-bit return type
    if (add(10, 20) !== 32'd30) begin
      $display("FAILED: add(10,20) returned %0d, expected 30", add(10, 20));
      $finish;
    end
    $display("PASSED");
  end
endmodule
