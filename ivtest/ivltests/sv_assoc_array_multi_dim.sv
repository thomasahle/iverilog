// Test for associative arrays with additional dimensions
// This tests that the compiler gives proper error messages instead of crashing
// for unsupported features like associative arrays of arrays

module test;
  // Simple associative array - should work
  bit [3:0] simple_assoc[int];

  // Associative array with fixed array dimension - currently not supported
  // but should give an error, not crash
  bit [3:0] complex_assoc[int][2];

  initial begin
    // Simple assoc access - works
    simple_assoc[4] = 4'hA;
    if (simple_assoc[4] == 4'hA)
      $display("PASSED: simple_assoc[4] = %h", simple_assoc[4]);
    else
      $display("FAILED: simple_assoc[4] = %h, expected hA", simple_assoc[4]);

    // Complex assoc access - should give error or warning
    // This was causing abort/segfault before the fix
    complex_assoc[4][0] = 4'hB;
    $display("complex_assoc[4][0] = %h", complex_assoc[4][0]);

    $display("PASSED");
  end
endmodule
