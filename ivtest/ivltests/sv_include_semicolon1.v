// Test that include directive with trailing semicolon works
// This is non-standard but commonly used in some testbenches

`define MY_MACRO 42

// Include with semicolon (non-standard but tolerated)
`include "sv_include_semicolon1_inc.vh";

module test;
  int my_val;
  int inc_val;

  initial begin
    my_val = `MY_MACRO;
    inc_val = `INCLUDED_VALUE;

    if (my_val !== 42) begin
      $display("FAILED: MY_MACRO = %0d, expected 42", my_val);
      $finish;
    end
    if (inc_val !== 100) begin
      $display("FAILED: INCLUDED_VALUE = %0d, expected 100", inc_val);
      $finish;
    end
    $display("PASSED");
  end
endmodule
