// Test calling a method on a class property object
// This pattern: obj.prop.method() where prop is an object
// Should properly switch the object context for the method call

module test;

  class Inner;
    int value;
    bit ready;

    function void set_value(int v);
      value = v;
      $display("Inner.set_value called with %0d", v);
    endfunction

    task wait_ready();
      $display("Inner.wait_ready called, ready=%0d", ready);
    endtask

    function int get_value();
      return value;
    endfunction
  endclass

  class Outer;
    string name;
    Inner inner_obj;

    function new(string n);
      name = n;
      inner_obj = new();
      inner_obj.value = 42;
      inner_obj.ready = 1;
    endfunction

    task call_inner_method();
      // This should call inner_obj's wait_ready with inner_obj as context
      inner_obj.wait_ready();
    endtask

    function void set_inner_value(int v);
      // This should call inner_obj's set_value with inner_obj as context
      inner_obj.set_value(v);
    endfunction

    function int get_inner_value();
      return inner_obj.get_value();
    endfunction
  endclass

  initial begin
    Outer o;
    int val;

    o = new("test_outer");

    // Direct property access
    $display("Direct access: inner_obj.value = %0d", o.inner_obj.value);

    // Call method on property object from outside
    o.inner_obj.set_value(100);
    $display("After set_value(100): inner_obj.value = %0d", o.inner_obj.value);

    // Call method that internally calls method on property object
    o.call_inner_method();

    // Call function that internally calls function on property object
    o.set_inner_value(200);
    $display("After set_inner_value(200): inner_obj.value = %0d", o.inner_obj.value);

    // Get value through nested call
    val = o.get_inner_value();
    $display("get_inner_value() returned: %0d", val);

    if (o.inner_obj.value == 200 && val == 200)
      $display("PASSED");
    else
      $display("FAILED");
  end

endmodule
