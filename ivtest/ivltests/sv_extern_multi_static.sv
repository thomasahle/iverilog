// Test extern constructor with multiple static and non-static methods
// This tests that the static method flag is properly reset between methods

package pkg;
  class calculator;
    int value;

    // Multiple extern declarations - mix of static and non-static
    extern function new(int init = 0);
    extern static function int add(int a, int b);
    extern function void set_value(int v);
    extern static function int multiply(int a, int b);
    extern function int get_value();
  endclass

  // Out-of-body definitions
  function calculator::new(int init = 0);
    value = init;
  endfunction

  function int calculator::add(int a, int b);
    return a + b;
  endfunction

  function void calculator::set_value(int v);
    value = v;
  endfunction

  function int calculator::multiply(int a, int b);
    return a * b;
  endfunction

  function int calculator::get_value();
    return value;
  endfunction
endpackage

module test;
  import pkg::*;

  initial begin
    calculator c;
    int result;

    // Test constructor
    c = new(10);
    if (c.get_value() != 10) begin
      $display("FAILED: constructor init, got %0d expected 10", c.get_value());
      $finish;
    end

    // Test static method after constructor
    result = calculator::add(5, 7);
    if (result != 12) begin
      $display("FAILED: add(5,7) returned %0d, expected 12", result);
      $finish;
    end

    // Test non-static method
    c.set_value(42);
    if (c.get_value() != 42) begin
      $display("FAILED: set_value/get_value, got %0d expected 42", c.get_value());
      $finish;
    end

    // Test another static method
    result = calculator::multiply(6, 7);
    if (result != 42) begin
      $display("FAILED: multiply(6,7) returned %0d, expected 42", result);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
