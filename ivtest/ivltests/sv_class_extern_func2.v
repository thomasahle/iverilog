// Test extern functions with various return types and parameter combinations
// This tests that extern declarations properly handle different signatures

class Calculator;
  extern function new();

  // Various return types
  extern function int add_int(int a, int b);
  extern function real add_real(real a, real b);
  extern function string format_result(int val);
  extern function bit is_positive(int val);
  extern function logic [31:0] shift_left(logic [31:0] val, int amount);

  // Void function
  extern function void print_banner();
endclass

function Calculator::new();
  $display("Calculator initialized");
endfunction

function int Calculator::add_int(int a, int b);
  return a + b;
endfunction

function real Calculator::add_real(real a, real b);
  return a + b;
endfunction

function string Calculator::format_result(int val);
  string s;
  $sformat(s, "Result = %0d", val);
  return s;
endfunction

function bit Calculator::is_positive(int val);
  return val > 0;
endfunction

function logic [31:0] Calculator::shift_left(logic [31:0] val, int amount);
  return val << amount;
endfunction

function void Calculator::print_banner();
  $display("=== Calculator ===");
endfunction

module test;
  initial begin
    Calculator calc;
    int i_result;
    real r_result;
    string s_result;
    bit b_result;
    logic [31:0] l_result;

    calc = new();
    calc.print_banner();

    i_result = calc.add_int(15, 27);
    if (i_result != 42) begin
      $display("FAILED: add_int=%0d, expected 42", i_result);
      $finish;
    end

    r_result = calc.add_real(3.14, 2.86);
    if (r_result < 5.99 || r_result > 6.01) begin
      $display("FAILED: add_real=%f, expected ~6.0", r_result);
      $finish;
    end

    s_result = calc.format_result(42);
    if (s_result != "Result = 42") begin
      $display("FAILED: format_result='%s'", s_result);
      $finish;
    end

    b_result = calc.is_positive(10);
    if (b_result != 1) begin
      $display("FAILED: is_positive(10)=%0d, expected 1", b_result);
      $finish;
    end

    b_result = calc.is_positive(-5);
    if (b_result != 0) begin
      $display("FAILED: is_positive(-5)=%0d, expected 0", b_result);
      $finish;
    end

    l_result = calc.shift_left(32'h0000000F, 4);
    if (l_result != 32'h000000F0) begin
      $display("FAILED: shift_left=%h, expected 000000F0", l_result);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
