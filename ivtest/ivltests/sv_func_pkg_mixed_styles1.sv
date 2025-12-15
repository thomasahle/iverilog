// Test: Mixed function declaration styles in package scope
// Tests that all function declaration variants work together in the same package
// Note: Per IEEE 1800, implicit return type defaults to 1-bit logic

package pkg;
  int global_counter = 0;

  // Style 1: Implicit return type, no parentheses (1-bit)
  function func_implicit_no_parens;
    func_implicit_no_parens = 1'b1;
  endfunction

  // Style 2: Implicit return type, empty parentheses (ANSI style) (1-bit)
  function func_implicit_ansi();
    func_implicit_ansi = 1'b1;
  endfunction

  // Style 3: Explicit int return type, ANSI style (32-bit)
  function int func_explicit_int();
    return 3;
  endfunction

  // Style 4: Explicit logic return type, old-style port declarations
  function logic [7:0] func_oldstyle_logic;
    input [3:0] hi;
    input [3:0] lo;
    func_oldstyle_logic = {hi, lo};
  endfunction

  // Style 5: Void function
  function void func_void();
    global_counter = global_counter + 1;
  endfunction
endpackage

module test;
  import pkg::*;

  initial begin
    // Test implicit return type, no parens (1-bit)
    if (func_implicit_no_parens() !== 1'b1) begin
      $display("FAILED: func_implicit_no_parens returned %0b", func_implicit_no_parens());
      $finish;
    end

    // Test implicit return type, empty parens (ANSI) (1-bit)
    if (func_implicit_ansi() !== 1'b1) begin
      $display("FAILED: func_implicit_ansi returned %0b", func_implicit_ansi());
      $finish;
    end

    // Test explicit int return type (32-bit)
    if (func_explicit_int() !== 3) begin
      $display("FAILED: func_explicit_int returned %0d", func_explicit_int());
      $finish;
    end

    // Test explicit logic return type with old-style ports
    if (func_oldstyle_logic(4'hA, 4'hB) !== 8'hAB) begin
      $display("FAILED: func_oldstyle_logic");
      $finish;
    end

    // Test void function (side effect only)
    func_void();

    $display("PASSED");
  end
endmodule
