// Test basic bind directive parsing and ignoring
// bind should be parsed but generate a warning

module target_module(input clk);
  logic [7:0] data;
endmodule

module assertions_mod(input clk);
  // Empty assertions module
endmodule

module top;
  logic clk;

  target_module t1(.clk(clk));

  // This bind should be parsed but ignored with a warning
  bind target_module assertions_mod A(.clk(clk));

  initial begin
    $display("PASSED: bind directive parsed and ignored");
  end
endmodule
