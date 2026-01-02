// Test wait() on class property expressions
// Uses polling loop implementation for class properties

module test;
  class Counter;
    int count = 0;
    bit done = 0;

    task increment();
      #5 count++;
    endtask

    task mark_done();
      #10 done = 1;
    endtask
  endclass

  Counter c;
  int pass = 1;

  initial begin
    c = new();

    // Fork processes
    fork
      // Process 1: increment count
      begin
        repeat(3) c.increment();
      end

      // Process 2: wait for count to reach 2
      begin
        wait(c.count >= 2);
        if (c.count < 2) begin
          $display("FAILED: wait(c.count >= 2) didn't work, count = %0d", c.count);
          pass = 0;
        end
      end

      // Process 3: mark done
      c.mark_done();

      // Process 4: wait for done
      begin
        wait(c.done);
        if (c.done !== 1) begin
          $display("FAILED: wait(c.done) didn't work, done = %0d", c.done);
          pass = 0;
        end
      end
    join

    if (pass)
      $display("PASSED");
  end
endmodule
