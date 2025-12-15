// Test: Local class type variable in task with wildcard import
// This tests the scenario where a class type from a wildcard-imported package
// is used as a local variable declaration inside a task body.

package pkg_a;
  class my_class;
    int x;
    function new();
      x = 42;
    endfunction
  endclass
endpackage

package pkg_b;
  import pkg_a::*;  // Wildcard import

  class test_class;
    task run();
      my_class obj;  // Local class type variable from imported package
      obj = new();
      if (obj.x == 42)
        $display("PASSED");
      else
        $display("FAILED: obj.x = %0d, expected 42", obj.x);
    endtask
  endclass
endpackage

module test;
  import pkg_b::*;

  initial begin
    test_class tc;
    tc = new();
    tc.run();
  end
endmodule
