// Test: Old-style function ports with explicit return type in package scope
// Tests the pattern used in DDR3 parameters file: function type name; input...; endfunction

package pkg;
  // Old-style function with explicit return type and old-style port declarations
  // Pattern: function return_type name; input declarations; statements; endfunction
  function logic valid_cl;
    input [3:0] cl;
    input [3:0] cwl;
    valid_cl = (cl == cwl);
  endfunction

  // Another old-style function with different return type
  function logic [7:0] compute;
    input [7:0] data;
    compute = {data[3:0], data[7:4]};  // Swap nibbles
  endfunction
endpackage

module test;
  import pkg::*;

  initial begin
    // Test valid_cl function
    if (valid_cl(6, 6) !== 1'b1) begin
      $display("FAILED: valid_cl(6,6) returned %0b, expected 1", valid_cl(6, 6));
      $finish;
    end
    if (valid_cl(6, 7) !== 1'b0) begin
      $display("FAILED: valid_cl(6,7) returned %0b, expected 0", valid_cl(6, 7));
      $finish;
    end

    // Test compute function
    if (compute(8'hAB) !== 8'hBA) begin
      $display("FAILED: compute(8'hAB) returned %0h, expected BA", compute(8'hAB));
      $finish;
    end

    $display("PASSED");
  end
endmodule
