// Test for sequence repetition operators (SV 16.9)
// Tests various forms of consecutive repetition [*n], [*m:n]
// Note: Some patterns involving expr ##N expr [*n] are not yet supported

module test;
  reg a = 0;
  reg b = 0;
  reg clk = 0;

  // Simple repetition works
  sequence s1;
    a [*2];
  endsequence

  // Range repetition works
  sequence s2;
    a [*2:10];
  endsequence

  // Repetition followed by delay works
  sequence s3;
    a [*2:10] ##1 b;
  endsequence

  // Delay followed by repetition works
  sequence s4;
    ##1 a [*2:10];
  endsequence

  // expr delay expr (without repetition) works
  sequence s5;
    b ##1 a;
  endsequence

  initial begin
    // Just test that parsing works
    $display("PASSED");
    $finish;
  end
endmodule
