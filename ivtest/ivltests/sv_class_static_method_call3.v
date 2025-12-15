// Test static method calls with return values used in expressions
// Tests both void calls as statements and calls with return values

class math;
  static function int add(int a, int b);
    return a + b;
  endfunction

  static function int mul(int a, int b);
    return a * b;
  endfunction

  static function int factorial(int n);
    int result = 1;
    for (int i = 1; i <= n; i++) begin
      result = result * i;
    end
    return result;
  endfunction
endclass

module test;
  int x, y, z;
  int errors = 0;

  initial begin
    // Static method with return value in assignment
    x = math::add(10, 20);
    if (x != 30) begin
      $display("FAILED: add(10,20)=%0d, expected 30", x);
      errors = errors + 1;
    end

    // Static method with return value in expression
    y = math::mul(3, 4) + math::add(5, 6);
    if (y != 23) begin
      $display("FAILED: mul(3,4)+add(5,6)=%0d, expected 23", y);
      errors = errors + 1;
    end

    // Nested static method calls
    z = math::add(math::mul(2, 3), math::mul(4, 5));
    if (z != 26) begin
      $display("FAILED: add(mul(2,3),mul(4,5))=%0d, expected 26", z);
      errors = errors + 1;
    end

    // Static method in condition
    if (math::factorial(5) != 120) begin
      $display("FAILED: factorial(5)=%0d, expected 120", math::factorial(5));
      errors = errors + 1;
    end

    if (errors == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d errors", errors);
    end
    $finish;
  end
endmodule
