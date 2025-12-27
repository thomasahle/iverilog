// Test nested task call on class properties
// This tests the case where one class calls a task on a child class object

class inner;
  int value;

  function new();
    value = 0;
  endfunction

  task run();
    value = 42;
    $display("inner run executed, value=%0d", value);
  endtask
endclass

class outer;
  inner child;

  function new();
    child = new();
  endfunction

  task run();
    child.run();
  endtask

  function int get_child_value();
    return child.value;
  endfunction
endclass

module test;
  initial begin
    automatic outer o;
    o = new();
    o.run();
    if (o.get_child_value() !== 42) begin
      $display("FAILED: child value is %0d, expected 42", o.get_child_value());
    end else begin
      $display("PASSED");
    end
  end
endmodule
