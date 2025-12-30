// Test bind directive with interface target
// The AXI4 AVIP uses interfaces for assertion binding

module target_module(input clk);
  logic [7:0] data;
endmodule

interface assertions_if(input clk);
  // Empty assertions interface
endinterface

module top;
  logic clk;

  target_module t1(.clk(clk));

  // Bind with interface type
  bind target_module assertions_if A(.clk(clk));

  initial begin
    $display("PASSED: bind with interface parsed and ignored");
  end
endmodule
