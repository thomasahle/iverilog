// Test division with different operand widths
module test;
  parameter FREQ = 10**9;  // 32-bit constant

  initial begin
    int clkPeriod;
    int result;
    bit [63:0] big_val;
    bit [7:0] small_val;

    clkPeriod = 100;

    // Division where operands may have different widths
    result = FREQ / clkPeriod;
    $display("FREQ / clkPeriod = %0d", result);

    // Another case
    big_val = 64'h1000_0000_0000;
    small_val = 8'd16;
    result = big_val / small_val;
    $display("big_val / small_val = %0d", result);

    // Division of 32-bit by 8-bit
    result = 1000 / small_val;
    $display("1000 / small_val = %0d", result);

    $display("PASSED");
  end
endmodule
