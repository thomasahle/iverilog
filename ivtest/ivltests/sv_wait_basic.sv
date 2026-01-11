// Test wait(expression) statement
module test;
  logic clk = 0;
  logic ready = 0;
  logic done = 0;
  int count = 0;

  always #5 clk = ~clk;

  // Process that waits for ready
  initial begin
    $display("Waiting for ready...");
    wait(ready);
    $display("Ready received at time %0t", $time);
    count++;
  end

  // Process that sets ready
  initial begin
    #25;
    ready = 1;
    #10;
    if (count == 1)
      $display("PASSED");
    else
      $display("FAILED: count=%0d", count);
    $finish;
  end
endmodule
