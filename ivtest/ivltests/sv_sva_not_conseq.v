// Test for SVA unary NOT in consequent
// https://github.com/anthropics/claude-code
module test;
  reg clk, rst, data;

  // Named property with NOT in consequent
  property p_not_conseq;
    @(posedge clk) rst |-> !data;
  endproperty

  // Assert the named property
  assert property (p_not_conseq);

  // Inline assertion with NOT in consequent
  assert property (@(posedge clk) rst |-> !data);

  initial begin
    clk = 0;
    rst = 0;
    data = 0;

    // Test case 1: rst=0, data=0 - should pass (antecedent false)
    #10;
    if (data !== 0) $error("Test setup failed");

    // Test case 2: rst=1, data=0 - should pass (!0 = 1)
    rst = 1;
    #20;

    // Test case 3: rst=1, data=1 - should fail (!1 = 0)
    data = 1;
    #20;

    $display("PASSED");
    $finish;
  end

  always #5 clk = ~clk;
endmodule
