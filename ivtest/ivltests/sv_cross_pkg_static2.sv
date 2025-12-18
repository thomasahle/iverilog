// Test cross-package static method calls with various import patterns
// Tests explicit import, wildcard import, and direct package:: access

package pkg_a;
  class counter;
    static int count = 0;
    static function int increment();
      count++;
      return count;
    endfunction
    static function int get_count();
      return count;
    endfunction
  endclass
endpackage

package pkg_b;
  class helper;
    static function int double(int x);
      return x * 2;
    endfunction
  endclass
endpackage

module test;
  import pkg_a::*;  // Wildcard import
  import pkg_b::helper;  // Explicit import

  initial begin
    int v1, v2, v3;

    // Test 1: Wildcard import static method
    v1 = counter::increment();
    if (v1 != 1) begin
      $display("FAILED: counter::increment() returned %0d, expected 1", v1);
      $finish;
    end

    // Test 2: Multiple static calls
    v2 = counter::increment();
    v3 = counter::get_count();
    if (v2 != 2 || v3 != 2) begin
      $display("FAILED: increment=%0d, get_count=%0d, expected 2,2", v2, v3);
      $finish;
    end

    // Test 3: Explicit import static method
    v1 = helper::double(21);
    if (v1 != 42) begin
      $display("FAILED: helper::double(21) returned %0d, expected 42", v1);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
