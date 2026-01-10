// Test disable fork - terminates all active forked processes
module test;
  int count;
  int step;

  initial begin
    count = 0;
    step = 0;

    fork
      begin
        #10;
        count = count + 1;
        step = 1;
      end
      begin
        #50;  // This should be killed by disable fork
        count = count + 1;
        step = 2;
      end
      begin
        #100;  // This should also be killed
        count = count + 1;
        step = 3;
      end
    join_none

    #20;  // Wait for first fork to complete
    disable fork;  // Kill remaining forked processes

    #90;  // Wait past when fork 2 and 3 would have completed

    // Only first fork should have completed
    if (count == 1 && step == 1)
      $display("PASSED");
    else
      $display("FAILED: count=%0d, step=%0d", count, step);
  end
endmodule
