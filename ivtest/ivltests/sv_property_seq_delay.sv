// Test that properties with sequence delays generate warnings instead of crashing
// Issue: Named properties with ##N delays caused segfault when elaborating
// with -gsupported-assertions flag

module test;
  logic clk, rstn, a, b, c;

  // Property with ##1 delay - should generate warning
  property checkProp;
    @(posedge clk) disable iff (!rstn)
    a |-> ##1 b;
  endproperty

  // Property with ##[range] delay - should generate warning
  property checkRange;
    @(posedge clk) a |-> ##[1:3] b;
  endproperty

  // Property with ##[m:$] unbounded delay - should generate warning
  property checkUnbounded;
    @(posedge clk) a |-> ##[1:$] b;
  endproperty

  // Simple property without delays - should work normally
  property simpleProp;
    @(posedge clk) a |-> b;
  endproperty

  // This should compile and run (simple implication)
  assert property (simpleProp);

  initial begin
    clk = 0;
    rstn = 1;
    a = 0;
    b = 0;
    c = 0;

    #5 clk = 1;
    #5 clk = 0;
    a = 1;
    b = 1;
    #5 clk = 1;
    #5 clk = 0;

    $display("PASSED");
    $finish;
  end
endmodule
