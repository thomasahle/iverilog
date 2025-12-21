// Test class property assignment
// This tests basic class property assignment and reading

module test;
  class InnerClass;
    int value;
    function new(int v = 0);
      value = v;
    endfunction
  endclass

  class OuterClass;
    InnerClass inner_h;
    InnerClass inner_arr[];

    function new();
      inner_h = null;
    endfunction

    function void set_inner(InnerClass i);
      inner_h = i;
    endfunction

    function int get_value();
      if (inner_h != null)
        return inner_h.value;
      return -1;
    endfunction
  endclass

  OuterClass outer;
  InnerClass inner;
  int result;

  initial begin
    // Test 1: Basic property assignment
    outer = new();
    inner = new(42);
    outer.inner_h = inner;
    result = outer.inner_h.value;
    if (result !== 42) begin
      $display("FAILED: Test 1 - Expected 42, got %0d", result);
      $finish;
    end
    $display("Test 1 PASSED: Basic property assignment works");

    // Test 2: Dynamic array of class handles
    outer.inner_arr = new[3];
    outer.inner_arr[0] = new(10);
    outer.inner_arr[1] = new(20);
    outer.inner_arr[2] = new(30);

    if (outer.inner_arr[1].value !== 20) begin
      $display("FAILED: Test 2 - Expected 20, got %0d", outer.inner_arr[1].value);
      $finish;
    end
    $display("Test 2 PASSED: Dynamic array property assignment works");

    // Test 3: Nested property through dynamic array
    outer.inner_arr[0].value = 100;
    if (outer.inner_arr[0].value !== 100) begin
      $display("FAILED: Test 3 - Expected 100, got %0d", outer.inner_arr[0].value);
      $finish;
    end
    $display("Test 3 PASSED: Nested property via dynamic array works");

    $display("PASSED");
  end
endmodule
