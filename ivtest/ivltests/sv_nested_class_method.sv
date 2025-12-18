// Test method call on nested class property
// Tests obj.class_prop.method() pattern

class inner_class;
  int value;
  function string sprint();
    return $sformatf("value=%0d", value);
  endfunction
  function new();
    value = 42;
  endfunction
endclass

class outer_class;
  inner_class inner;
  function new();
    inner = new();
  endfunction
endclass

module test;
  initial begin
    outer_class outer;
    string s;
    outer = new();
    s = outer.inner.sprint();
    $display("%s", s);
    if (s == "value=42")
      $display("PASSED");
    else
      $display("FAILED: got %s", s);
    $finish;
  end
endmodule
