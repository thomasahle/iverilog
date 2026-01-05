// Simplest concurrent assertion test

module test;
  reg a;
  int count;

  initial begin
    a = 0;
    count = 0;

    // Test simple immediate assertion (should work)
    assert (1 == 1)
      count++;
    else
      $error("1==1 failed");

    // Now test concurrent assertion without clocking event
    assert property (a == 0)
      count++;
    else
      $error("a==0 failed");

    a = 1;

    assert property (a == 1)
      count++;
    else
      $error("a==1 failed");

    $display("Count: %0d", count);
    if (count == 3)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
