// Test for property local variables (SV 16.10)
// This tests the parsing of local variables and sequence match items

module test;
  logic clk = 0;
  logic valid = 1;
  logic [7:0] data = 8'h42;

  // Property with local variable declaration
  property prop_local;
    int x;
    @(posedge clk) (valid, x = data) |-> ##1 (x == data);
  endproperty

  // Sequence with local variable
  sequence seq_local;
    int y;
    (valid, y = data) ##1 (valid);
  endsequence

  // Simple property without local vars (control)
  property prop_simple;
    @(posedge clk) valid |-> ##1 valid;
  endproperty

  // Use assert property (will be ignored due to local var elaboration limitation)
  // assert property (prop_local);

  // Generate clock
  always #5 clk = ~clk;

  initial begin
    // Just test parsing - semantic support is not yet implemented
    #100;
    $display("PASSED");
    $finish;
  end

endmodule
