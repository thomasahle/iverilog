// Test SVA bind statement parsing
// IEEE 1800-2017 Section 23.11

module target_mod(input clk, input data);
  reg internal;
  always @(posedge clk) internal <= data;
endmodule

module checker_mod(input clk, input data);
  // Simple checker module
  initial $display("checker_mod instantiated");
endmodule

module top;
  reg clk, data;

  target_mod target(.clk(clk), .data(data));

  // SVA bind statement - binds checker_mod to all instances of target_mod
  bind target_mod checker_mod my_checker(.clk(clk), .data(data));

  initial begin
    clk = 0;
    data = 0;
    #100 $display("PASSED");
    $finish;
  end

  always #5 clk = ~clk;
endmodule
