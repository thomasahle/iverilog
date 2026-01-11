// Test wait with OR expression
module test;
  logic clk = 0;
  logic cond_a = 0;
  logic cond_b = 0;
  int which = 0;

  always #5 clk = ~clk;

  // Wait for either condition
  initial begin
    $display("Waiting for cond_a || cond_b...");
    wait(cond_a || cond_b);
    if (cond_a) which = 1;
    else if (cond_b) which = 2;
    $display("Condition met at time %0t (which=%0d)", $time, which);
  end

  // Set cond_b first (not cond_a)
  initial begin
    #25;
    cond_b = 1;  // This should trigger the wait
    #10;
    if (which == 2)
      $display("PASSED");
    else
      $display("FAILED: which=%0d", which);
    $finish;
  end
endmodule
