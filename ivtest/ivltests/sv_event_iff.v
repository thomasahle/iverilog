// Test for event iff conditional parsing (SV 9.4.2.3)
// Tests @(posedge clk iff enable) syntax
// Note: This tests parsing only - iff semantics are not yet implemented

module test;
  reg clk = 0;
  reg enable = 0;
  reg a = 0;

  // Various event iff syntaxes - parsing test
  always @(posedge clk iff enable)
    a <= ~a;

  always @(negedge clk iff enable == 1)
    a <= a;

  initial begin
    // Just test that parsing works
    $display("PASSED");
    $finish;
  end
endmodule
