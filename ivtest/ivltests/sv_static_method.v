// Test static class method calls using ClassName::method() syntax
// This tests that static methods can be called through class scope resolution

package test_pkg;
  class converter;
    static function int double_it(int a);
      return a * 2;
    endfunction

    static function int add_values(int a, int b);
      return a + b;
    endfunction
  endclass

  class math_helper;
    static function int multiply(int a, int b);
      return a * b;
    endfunction
  endclass
endpackage

module test;
  import test_pkg::*;

  initial begin
    int x, y, z;

    // Test static function call with single argument
    x = converter::double_it(5);
    if (x !== 10) begin
      $display("FAILED: double_it(5) = %0d, expected 10", x);
      $finish;
    end

    // Test static function call with multiple arguments
    y = converter::add_values(3, 7);
    if (y !== 10) begin
      $display("FAILED: add_values(3, 7) = %0d, expected 10", y);
      $finish;
    end

    // Test different class static method
    z = math_helper::multiply(4, 5);
    if (z !== 20) begin
      $display("FAILED: multiply(4, 5) = %0d, expected 20", z);
      $finish;
    end

    // Test chained calculations
    x = converter::double_it(math_helper::multiply(2, 3));
    if (x !== 12) begin
      $display("FAILED: double_it(multiply(2, 3)) = %0d, expected 12", x);
      $finish;
    end

    $display("PASSED");
  end
endmodule
