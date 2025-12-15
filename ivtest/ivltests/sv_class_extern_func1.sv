// Test basic extern function declaration with out-of-body definition
// This tests the fundamental extern/out-of-line method syntax

class MyClass;
  int value;

  extern function new(string name);
  extern function int get_value();
  extern function void set_value(int v);
endclass

function MyClass::new(string name);
  value = 0;
  $display("MyClass::new called with name='%s'", name);
endfunction

function int MyClass::get_value();
  return value;
endfunction

function void MyClass::set_value(int v);
  value = v;
endfunction

module test;
  initial begin
    MyClass obj;
    obj = new("test_obj");

    if (obj.get_value() != 0) begin
      $display("FAILED: initial value=%0d, expected 0", obj.get_value());
      $finish;
    end

    obj.set_value(42);

    if (obj.get_value() != 42) begin
      $display("FAILED: value=%0d, expected 42", obj.get_value());
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
