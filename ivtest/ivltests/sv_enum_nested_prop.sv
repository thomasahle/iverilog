// Test enum method chaining through nested class properties
// This tests obj.class_prop.enum_prop.name() pattern

typedef enum {RED, GREEN, BLUE} color_e;

class inner_class;
  color_e my_color;
  function new();
    my_color = GREEN;
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
    // Test nested access: outer.inner.my_color.name()
    s = outer.inner.my_color.name();
    $display("color=%s", s);
    if (s == "GREEN")
      $display("PASSED");
    else
      $display("FAILED: expected GREEN, got %s", s);
    $finish;
  end
endmodule
