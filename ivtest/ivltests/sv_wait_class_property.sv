// Test workaround for wait on class property
// wait() on class properties is not supported, use polling loop instead

module test;
  class workaround_class;
    bit flag;

    task wait_for_flag_workaround();
      // Use polling loop as workaround for wait(class_property)
      while (!flag) #1;
      $display("Flag is set!");
    endtask

    task set_flag();
      #10;
      flag = 1;
    endtask
  endclass

  workaround_class obj;

  initial begin
    obj = new();
    fork
      obj.wait_for_flag_workaround();
      obj.set_flag();
    join
    $display("PASSED");
  end
endmodule
