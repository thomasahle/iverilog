// Test for tagged union parsing (SV 11.9)
module test;
  // Simple tagged union - all members have data
  typedef union tagged {
    int A;
    int B;
    int C;
  } Variant;

  initial begin
    $display("PASSED - tagged union syntax accepted");
  end
endmodule
