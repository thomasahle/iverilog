// Test fork/join_none parallel execution
// This tests UVM-style parallel run_phase execution

class worker;
  string name;
  int done;

  function new(string n);
    name = n;
    done = 0;
  endfunction

  task run();
    $display("%s: starting at %0t", name, $time);
    #10;
    $display("%s: done at %0t", name, $time);
    done = 1;
  endtask
endclass

// Helper task with automatic storage for proper variable capture
task automatic fork_worker_run(worker w);
  fork
    w.run();
  join_none
endtask

module test;
  initial begin
    worker w0, w1, w2;

    // Create workers
    w0 = new("worker0");
    w1 = new("worker1");
    w2 = new("worker2");

    // Fork all workers in parallel using helper task
    fork_worker_run(w0);
    fork_worker_run(w1);
    fork_worker_run(w2);

    // Wait a bit to let forks start
    #0;

    // Wait for all to complete
    #20;

    // Check all completed
    if (w0.done && w1.done && w2.done) begin
      $display("PASSED");
    end else begin
      $display("FAILED: not all workers completed");
    end
  end
endmodule
