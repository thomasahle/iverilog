// Test interface instantiation with port connections
// This tests that interfaces with ports can be instantiated inside modules

interface TestIface(input bit clk, input bit rst);
  logic [7:0] data;

  // Simple behavior using interface ports
  always @(posedge clk) begin
    if (rst) data <= 8'h00;
  end
endinterface

module test;
  bit clk, rst;

  // Interface instantiation with port connections
  TestIface u_if(clk, rst);

  initial begin
    clk = 0;
    rst = 1;
    u_if.data = 8'hFF;

    #1 clk = 1;  // Rising edge with reset
    #1 clk = 0;

    if (u_if.data === 8'h00)
      $display("PASSED");
    else
      $display("FAILED: data=%h (expected 00)", u_if.data);
  end
endmodule
