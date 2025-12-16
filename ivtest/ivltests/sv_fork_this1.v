// Test fork/join_none with class method accessing 'this'
// This tests the fork_this mechanism that preserves 'this' across context switches

class Counter;
  int value;

  function new(int init_val);
    value = init_val;
  endfunction

  task increment_async();
    fork
      begin
        #1;
        value = value + 1;
        $display("After increment: value = %0d", value);
      end
    join_none
  endtask
endclass

module test;
  initial begin
    Counter c = new(10);

    $display("Initial: value = %0d", c.value);
    c.increment_async();
    #5;

    if (c.value !== 11) begin
      $display("FAILED: expected value=11, got %0d", c.value);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
