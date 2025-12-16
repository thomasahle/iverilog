// Test fork/join_none with nested function calls accessing 'this'
// This tests fork_this propagation through function call chains

class DataProcessor;
  int data;
  int processed_count;

  function new(int init_data);
    data = init_data;
    processed_count = 0;
  endfunction

  // Forked task that calls helper functions
  task process_async();
    fork
      begin
        do_process();
      end
    join_none
  endtask

  task do_process();
    // Call a function - this exercises fork_this propagation
    int result = compute_value();
    data = result;
    increment_count();
    $display("do_process: data=%0d, count=%0d", data, processed_count);
  endtask

  function int compute_value();
    // Access 'this' from within function called by forked task
    return data * 2;
  endfunction

  function void increment_count();
    // Another function accessing 'this'
    processed_count = processed_count + 1;
  endfunction
endclass

module test;
  initial begin
    DataProcessor dp = new(5);

    $display("Initial: data=%0d, count=%0d", dp.data, dp.processed_count);
    dp.process_async();
    #1;

    if (dp.data !== 10) begin
      $display("FAILED: expected data=10, got %0d", dp.data);
      $finish;
    end
    if (dp.processed_count !== 1) begin
      $display("FAILED: expected count=1, got %0d", dp.processed_count);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
