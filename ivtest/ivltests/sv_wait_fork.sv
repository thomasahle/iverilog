// Test wait fork - waits for all forked processes to complete
module test;
  int count;

  initial begin
    count = 0;

    fork
      begin
        #10;
        count = count + 1;
      end
      begin
        #20;
        count = count + 1;
      end
      begin
        #30;
        count = count + 1;
      end
    join_none

    // At this point, no forks have completed yet
    if (count != 0) begin
      $display("FAILED: count=%0d after join_none, expected 0", count);
      $finish;
    end

    wait fork;

    // After wait fork, all forks should be complete
    if (count == 3)
      $display("PASSED");
    else
      $display("FAILED: count=%0d after wait fork, expected 3", count);
  end
endmodule
