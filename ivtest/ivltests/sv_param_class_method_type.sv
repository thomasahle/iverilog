// Test parameterized class method specialization with type parameter.
// When a class is parameterized with a type (e.g., Container#(Item)),
// methods must use the specialized type for parameters and return values.

class Item;
  int value;
  function new(int v);
    value = v;
  endfunction
endclass

class Container #(type T = int);
  T data;

  function void set(T val);
    data = val;
  endfunction

  function T get();
    return data;
  endfunction
endclass

module test;
  initial begin
    automatic Container#(Item) c;
    automatic Item i;
    automatic Item result;

    c = new();
    i = new(42);

    // Test set method with specialized type parameter
    c.set(i);

    // Test get method returning specialized type
    result = c.get();

    if (result == null) begin
      $display("FAILED: get() returned null");
      $finish;
    end

    if (result.value == 42)
      $display("PASSED");
    else
      $display("FAILED: expected 42, got %0d", result.value);

    $finish;
  end
endmodule
