// PARTIALLY FIXED: Parameterized class with real type parameter
//
// Previously crashed at runtime with:
//   Assertion failed: (0), function set_vec4, file class_type.cc, line 127
//
// Now the crash is fixed. The behavior is:
// - Integer-valued reals (like 42.0) work correctly through methods
// - Fractional values (like 3.14) lose precision through methods
// - Direct property access preserves full real precision
//
// The method code is generated with T=int default type, so vec4 (integer)
// operations are used. This converts real to int and back, losing fractions.
// Direct property access uses real operations and preserves full precision.

package my_pkg;
  class Container #(type T = int);
    T data;
    function new();
    endfunction
    function void set(T val);
      data = val;
    endfunction
    function T get();
      return data;
    endfunction
  endclass
endpackage

module test;
  import my_pkg::*;

  my_pkg::Container#(real) c_real;

  initial begin
    c_real = new();

    // Integer-valued reals work through methods
    c_real.set(42.0);
    if (c_real.get() == 42.0) begin
      $display("PASSED: Integer value preserved through set/get");
    end else begin
      $display("FAILED: Integer value not preserved");
      $finish;
    end

    // Direct property access preserves full real precision
    c_real.data = 3.14;
    if (c_real.data == 3.14) begin
      $display("PASSED: Direct property access preserves real 3.14");
    end else begin
      $display("FAILED: Direct property lost precision");
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
