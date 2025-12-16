// Test const ref parameter in functions and tasks
// IEEE 1800-2005: const ref is a special port direction

module test;

  // Test with simple types - function with const ref
  function automatic int add_to_ref(const ref int a, input int b);
    return a + b;
  endfunction

  // Task with const ref parameter
  task automatic display_value(const ref int val);
    $display("Value: %0d", val);
  endtask

  // Task with ref parameter (can modify)
  task automatic increment_value(ref int val);
    val = val + 1;
  endtask

  int x;
  int result;

  initial begin
    x = 10;

    // Test const ref with simple type in function
    result = add_to_ref(x, 5);
    if (result !== 15) begin
      $display("FAILED: add_to_ref returned %0d, expected 15", result);
      $finish;
    end

    // Test task with const ref
    display_value(x);

    // Test task with ref (modification)
    increment_value(x);
    if (x !== 11) begin
      $display("FAILED: increment_value didn't modify x, got %0d", x);
      $finish;
    end

    $display("PASSED");
  end
endmodule
