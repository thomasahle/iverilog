// Test case: Variable index method call on dynamic array class property
// Tests both simple and nested chains: arr[i].method(), arr[i].member.method()
package test_pkg;
  class inner_class;
    int value;

    function new(int v = 0);
      value = v;
    endfunction

    function void hello();
      $display("Hello from inner class, value=%0d", value);
    endfunction

    function int get_value();
      return value;
    endfunction
  endclass

  class middle_class;
    inner_class inner;

    function new(int v = 0);
      inner = new(v);
    endfunction
  endclass

  class outer_class;
    inner_class simple_arr[];    // For simple arr[i].method() tests
    middle_class nested_arr[];   // For nested arr[i].member.method() tests

    function new(int size);
      simple_arr = new[size];
      nested_arr = new[size];
      for (int i = 0; i < size; i++) begin
        simple_arr[i] = new(i * 10);
        nested_arr[i] = new(i * 100);
      end
    endfunction

    // Simple: arr[i].method()
    function void call_simple_tasks();
      for (int i = 0; i < simple_arr.size(); i++) begin
        simple_arr[i].hello();
      end
    endfunction

    function int get_simple_value(int idx);
      return simple_arr[idx].get_value();
    endfunction

    // Nested: arr[i].member.method()
    function void call_nested_tasks();
      for (int i = 0; i < nested_arr.size(); i++) begin
        nested_arr[i].inner.hello();
      end
    endfunction

    function int get_nested_value(int idx);
      return nested_arr[idx].inner.get_value();
    endfunction
  endclass
endpackage

module test;
  import test_pkg::*;

  outer_class obj;
  int sum;

  initial begin
    obj = new(3);

    $display("=== Simple arr[i].method() tests ===");
    obj.call_simple_tasks();

    sum = 0;
    for (int i = 0; i < 3; i++) begin
      $display("Simple element %0d value: %0d", i, obj.get_simple_value(i));
      sum += obj.get_simple_value(i);
    end
    // Expected: 0 + 10 + 20 = 30
    if (sum != 30) begin
      $display("FAILED: Simple test expected sum=30, got sum=%0d", sum);
      $finish;
    end

    $display("=== Nested arr[i].member.method() tests ===");
    obj.call_nested_tasks();

    sum = 0;
    for (int i = 0; i < 3; i++) begin
      $display("Nested element %0d value: %0d", i, obj.get_nested_value(i));
      sum += obj.get_nested_value(i);
    end
    // Expected: 0 + 100 + 200 = 300
    if (sum != 300) begin
      $display("FAILED: Nested test expected sum=300, got sum=%0d", sum);
      $finish;
    end

    $display("PASSED");
  end
endmodule
