// Test: interface instantiation with named port connections
// This tests interface with .name(signal) connections

interface ClockIface(input wire clk, input wire rst_n);
  logic [7:0] data;
  logic valid;

  // Simple clocked behavior
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      valid <= 0;
  end
endinterface

module test;
  reg clock;
  reg reset_n;

  // Interface with named port connections
  ClockIface u_if(.clk(clock), .rst_n(reset_n));

  initial begin
    clock = 0;
    reset_n = 0;
    #5 reset_n = 1;
    #10;

    u_if.data = 8'hAA;
    u_if.valid = 1;

    #1;
    if (u_if.data !== 8'hAA || u_if.valid !== 1) begin
      $display("FAILED: data=%h valid=%b", u_if.data, u_if.valid);
      $finish;
    end
    $display("PASSED");
    $finish;
  end

  always #5 clock = ~clock;
endmodule
