// Test: Function with implicit return type (no return type specified) in package scope
// This tests old-style function declarations without return type in packages
// Note: Per IEEE 1800, implicit return type defaults to 1-bit logic

package pkg;
  // Old-style function with implicit return type (defaults to 1-bit logic)
  // This syntax was previously failing in package scope with a syntax error
  function foo;
    foo = 1'b1;  // Return 1-bit value
  endfunction

  // Test the assignment works by returning 0
  function bar;
    bar = 1'b0;  // Return 1-bit value
  endfunction
endpackage

module test;
  import pkg::*;

  initial begin
    if (foo() !== 1'b1) begin
      $display("FAILED: foo() returned %0b, expected 1", foo());
      $finish;
    end
    if (bar() !== 1'b0) begin
      $display("FAILED: bar() returned %0b, expected 0", bar());
      $finish;
    end
    $display("PASSED");
  end
endmodule
