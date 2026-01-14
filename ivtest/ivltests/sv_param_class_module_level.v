// Test parameterized class at module level
// This tests the grammar rule for:
//   package_scope TYPE_IDENTIFIER '#' '(' params ')' var_name ';'
// Note: Requires explicit package scope (e.g., my_pkg::Container#(int))
// Note: Real type parameters have a known bug (set_vec4 assertion)

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

  // Parameterized class at module level (requires explicit package scope)
  my_pkg::Container#(int) c1;
  my_pkg::Container#(int) c2;

  initial begin
    // Test first int container
    c1 = new();
    c1.set(42);
    if (c1.get() != 42) begin
      $display("FAILED: c1 got %0d, expected 42", c1.get());
      $finish;
    end

    // Test second int container
    c2 = new();
    c2.set(100);
    if (c2.get() != 100) begin
      $display("FAILED: c2 got %0d, expected 100", c2.get());
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
