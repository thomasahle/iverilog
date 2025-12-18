// Test method call without parentheses in nested class access
// Pattern: this.member.method where member is a class object

class Inner;
  int value;

  function new(int v = 0);
    value = v;
  endfunction

  // Method with default parameter
  function string sprint(string prefix = "");
    return $sformatf("%sInner{value=%0d}", prefix, value);
  endfunction

  function int get_value(int offset = 0);
    return value + offset;
  endfunction
endclass

class Outer;
  Inner inner_obj;

  function new();
    inner_obj = new(42);
  endfunction

  task test_nested_access();
    string s;
    int v;

    // Test nested method call without parens: this.inner_obj.sprint
    s = inner_obj.sprint;
    $display("Test 1 - nested sprint: %s", s);
    if (s != "Inner{value=42}") begin
      $display("FAILED: Test 1");
      $finish;
    end

    // Test nested method call without parens: this.inner_obj.get_value
    v = inner_obj.get_value;
    $display("Test 2 - nested get_value: %0d", v);
    if (v != 42) begin
      $display("FAILED: Test 2");
      $finish;
    end

    $display("PASSED");
  endtask
endclass

module test;
  Outer outer_obj;

  initial begin
    outer_obj = new();
    outer_obj.test_nested_access();
    $finish;
  end
endmodule
