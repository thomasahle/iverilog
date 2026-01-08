// Test parameterized class method call with type parameter
// Verifies that Container#(int) correctly handles int-typed methods
package test_pkg;

class Container #(type T = int);
  T value;

  function void write(T val);
    value = val;
    $display("Wrote value: %0d", value);
  endfunction

  function T read();
    return value;
  endfunction
endclass

endpackage

module test;
  import test_pkg::*;

  // Use explicit package scope
  test_pkg::Container#(int) c_int;

  initial begin
    // Test integer container
    c_int = new;
    c_int.write(42);
    $display("Read value: %0d", c_int.read());
    $display("PASSED");
  end
endmodule
