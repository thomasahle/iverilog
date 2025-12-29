// Test printing queues and objects with $sformatf
// Verifies that queue/class arguments don't crash the compiler

module test;
  int errors = 0;

  class SimpleClass;
    int value;
    function new(int v);
      value = v;
    endfunction
  endclass

  initial begin
    int q1[$];
    string result;
    SimpleClass obj;

    q1 = '{1, 2, 3};
    obj = new(42);

    // Test 1: Print queue with %p format (should show placeholder)
    result = $sformatf("Queue value: %p", q1);
    $display("Test 1 result: %s", result);
    if (result != "") begin
      $display("PASS: Queue can be passed to $sformatf");
    end else begin
      $display("FAIL: $sformatf returned empty string");
      errors++;
    end

    // Test 2: Print class object with %p format (should show placeholder)
    result = $sformatf("Object value: %p", obj);
    $display("Test 2 result: %s", result);
    if (result != "") begin
      $display("PASS: Object can be passed to $sformatf");
    end else begin
      $display("FAIL: $sformatf returned empty string");
      errors++;
    end

    // Report results
    $display("");
    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);

    $finish;
  end
endmodule
