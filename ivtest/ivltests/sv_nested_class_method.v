// Test method calls on nested class properties
// Pattern: obj.nested_class_prop.method()

class Inner;
  int value;

  function new(int v);
    value = v;
  endfunction

  function string get_info();
    return $sformatf("Inner(value=%0d)", value);
  endfunction

  function int get_value();
    return value;
  endfunction
endclass

class Outer;
  Inner inner;
  string name;

  function new(string n, int v);
    name = n;
    inner = new(v);
  endfunction

  function string get_inner_info();
    return inner.get_info();
  endfunction
endclass

module test;
  initial begin
    Outer o;
    string s;
    int v;

    o = new("test", 42);

    // Test nested method call
    s = o.inner.get_info();
    if (s != "Inner(value=42)") begin
      $display("FAILED: o.inner.get_info() = %s", s);
      $finish;
    end

    // Test nested method returning int
    v = o.inner.get_value();
    if (v != 42) begin
      $display("FAILED: o.inner.get_value() = %0d", v);
      $finish;
    end

    // Test wrapper method
    s = o.get_inner_info();
    if (s != "Inner(value=42)") begin
      $display("FAILED: o.get_inner_info() = %s", s);
      $finish;
    end

    $display("PASSED");
  end
endmodule
