// Test extern function/task out-of-body definitions
// This tests the SystemVerilog feature where class methods can be declared
// as extern and defined outside the class body.

class Calculator;
  int accumulator;

  // Extern function declarations
  extern function int add(int val);
  extern function int get_value();
  extern function void reset();
  extern task delay_add(int val, int delay_cycles);

  function new();
    accumulator = 0;
  endfunction
endclass

// Out-of-body function definitions
function int Calculator::add(int val);
  accumulator = accumulator + val;
  return accumulator;
endfunction

function int Calculator::get_value();
  return accumulator;
endfunction

function void Calculator::reset();
  accumulator = 0;
endfunction

task Calculator::delay_add(int val, int delay_cycles);
  #(delay_cycles);
  accumulator = accumulator + val;
endtask

module test;
  Calculator calc;
  int result;
  int passed;

  initial begin
    passed = 1;
    calc = new();

    // Test 1: Initial value should be 0
    if (calc.get_value() != 0) begin
      $display("FAILED: Test 1 - Initial value = %0d, expected 0", calc.get_value());
      passed = 0;
    end

    // Test 2: Add values
    result = calc.add(10);
    if (result != 10) begin
      $display("FAILED: Test 2a - add(10) returned %0d, expected 10", result);
      passed = 0;
    end

    result = calc.add(5);
    if (result != 15) begin
      $display("FAILED: Test 2b - add(5) returned %0d, expected 15", result);
      passed = 0;
    end

    // Test 3: Get value
    if (calc.get_value() != 15) begin
      $display("FAILED: Test 3 - get_value() = %0d, expected 15", calc.get_value());
      passed = 0;
    end

    // Test 4: Reset
    calc.reset();
    if (calc.get_value() != 0) begin
      $display("FAILED: Test 4 - After reset, get_value() = %0d, expected 0", calc.get_value());
      passed = 0;
    end

    // Test 5: Task with delay
    calc.delay_add(100, 10);
    if (calc.get_value() != 100) begin
      $display("FAILED: Test 5 - After delay_add, get_value() = %0d, expected 100", calc.get_value());
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
