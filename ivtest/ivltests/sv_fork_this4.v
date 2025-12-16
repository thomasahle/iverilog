// Test multiple fork/join_none from same object
// Each forked task should access the same 'this'

class MultiTasker;
  int counter;
  int task_a_ran;
  int task_b_ran;

  function new();
    counter = 0;
    task_a_ran = 0;
    task_b_ran = 0;
  endfunction

  task run_both();
    fork
      task_a();
      task_b();
    join_none
  endtask

  task task_a();
    #1;
    counter = counter + 10;
    task_a_ran = 1;
    $display("task_a: counter = %0d", counter);
  endtask

  task task_b();
    #2;
    counter = counter + 20;
    task_b_ran = 1;
    $display("task_b: counter = %0d", counter);
  endtask
endclass

module test;
  initial begin
    MultiTasker mt = new();

    mt.run_both();
    #5;

    if (mt.task_a_ran !== 1) begin
      $display("FAILED: task_a did not run");
      $finish;
    end
    if (mt.task_b_ran !== 1) begin
      $display("FAILED: task_b did not run");
      $finish;
    end
    if (mt.counter !== 30) begin
      $display("FAILED: expected counter=30, got %0d", mt.counter);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
