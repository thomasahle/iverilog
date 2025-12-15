// Test interface instantiation with empty parentheses
// This is valid SystemVerilog syntax: InterfaceName inst_name();

interface TestIface;
  logic [7:0] data;
  logic clk;
endinterface

module test;
  // Interface instantiation with parentheses
  TestIface u_if();

  initial begin
    u_if.data = 8'hAB;
    #1;
    if (u_if.data === 8'hAB)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
