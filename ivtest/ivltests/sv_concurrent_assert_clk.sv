// Test concurrent assertion with clocking event

module test;
  reg clk;
  reg a, b;
  int pass_count, fail_count;

  // Generate clock
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test concurrent assertion WITH explicit clocking event
  // This assertion samples on posedge clk
  initial begin
    a = 0; b = 0;
    pass_count = 0;
    fail_count = 0;

    // Wait for first edge
    @(posedge clk);

    // Test with clocking event - should check a && b at each posedge
    assert property (@(posedge clk) a && b)
      pass_count++;
    else
      fail_count++;

    // Still both low - should fail
    @(posedge clk);
    assert property (@(posedge clk) a && b)
      pass_count++;
    else
      fail_count++;

    a = 1; b = 1;
    @(posedge clk);

    // Now both high - should pass
    assert property (@(posedge clk) a && b)
      pass_count++;
    else
      fail_count++;

    @(posedge clk);
    assert property (@(posedge clk) a && b)
      pass_count++;
    else
      fail_count++;

    $display("Pass: %0d, Fail: %0d", pass_count, fail_count);

    if (pass_count >= 2 && fail_count >= 2)
      $display("PASSED");
    else
      $display("FAILED: expected at least 2 passes and 2 fails");

    $finish;
  end
endmodule
