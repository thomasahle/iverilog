// Test labeled endinterface syntax
// This tests that endinterface can have a label matching the interface name

interface TestIface;
  logic [7:0] data;
  logic clk;
endinterface : TestIface  // Labeled endinterface

module test;
  // Note: Interface instances require parentheses in Icarus
  TestIface u_if();

  initial begin
    u_if.data = 8'h55;
    #1;
    if (u_if.data === 8'h55)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule : test  // Also test labeled endmodule
