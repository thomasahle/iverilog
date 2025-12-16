// Test ref in functions (IEEE 1800-2012 13.4.1)
// Verify parsing of ref arguments in functions

module test;

  // Task with ref (tasks have always supported ref)
  task automatic swap_task(ref int a, ref int b);
    int temp;
    temp = a;
    a = b;
    b = temp;
  endtask

  // Function with ref - verify it parses (may have runtime issues)
  function automatic int func_with_ref(ref int x);
    return x + 1;
  endfunction

  // Function with const ref - should work correctly
  function automatic int func_with_const_ref(const ref int x);
    return x * 2;
  endfunction

  // Function with mixed const ref and ref
  function automatic int mixed_refs(const ref int src, ref int dst);
    dst = src;
    return src + dst;
  endfunction

  int a, b;
  int result;

  initial begin
    a = 5;
    b = 10;

    // Test task with ref (always worked)
    swap_task(a, b);
    if (a !== 10 || b !== 5) begin
      $display("FAILED: swap_task, a=%0d b=%0d", a, b);
      $finish;
    end

    // Test function with const ref
    result = func_with_const_ref(a);
    if (result !== 20) begin
      $display("FAILED: func_with_const_ref returned %0d, expected 20", result);
      $finish;
    end

    // Verify functions with ref at least parse and run
    result = func_with_ref(a);
    $display("func_with_ref(10) = %0d", result);

    $display("PASSED");
  end
endmodule
