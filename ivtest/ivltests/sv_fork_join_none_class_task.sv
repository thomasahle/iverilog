// Test fork/join_none in class tasks

class Driver;
   int count;
   bit done;

   function new();
      count = 0;
      done = 0;
   endfunction

   task run();
      $display("run() starting");
      fork
         begin
            $display("Forked task A starting");
            #10;
            count = count + 1;
            $display("Forked task A done, count=%0d", count);
         end
         begin
            $display("Forked task B starting");
            #20;
            count = count + 10;
            $display("Forked task B done, count=%0d", count);
         end
      join_none
      $display("run() continuing after fork/join_none");
      #5;
      $display("run() after #5, count=%0d", count);
      done = 1;
   endtask
endclass

module test;
   Driver drv;

   initial begin
      drv = new();
      drv.run();
      $display("After run(), done=%0d", drv.done);

      // Wait for forked tasks to complete
      #30;
      $display("Final count=%0d", drv.count);

      if (drv.count == 11 && drv.done == 1) begin
         $display("PASSED");
      end else begin
         $display("FAILED: expected count=11, done=1, got count=%0d, done=%0d", drv.count, drv.done);
      end
      $finish;
   end
endmodule
