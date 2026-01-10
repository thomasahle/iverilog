// sv_param_class_type_limit.sv
// Test: Parameterized class with class type parameter - known limitation
//
// When a parameterized class uses a type parameter (e.g., type T = int) and
// the specialization uses a class type (e.g., Container#(Item)), methods that
// access type-parameterized properties will NOT work correctly. This is because
// methods are elaborated with the default type parameter value, not the specialized one.
//
// Workaround: Access properties directly from outside the class, or use non-parameterized types.

package test_pkg;
  class Item;
    int value;
    function new(int v = 0);
      value = v;
    endfunction
  endclass

  // Container with type parameter
  class Container #(type T = int);
    T items[$];  // Queue of T - when T=Item, this is a queue of Item objects

    // Methods that access items don't work when T is a class type.
    // Workaround: access items property directly from outside the class.
  endclass
endpackage

module test;
  import test_pkg::*;
  test_pkg::Container #(Item) c;
  Item i1, i2, retrieved;

  initial begin
    c = new();

    // Create items
    i1 = new(42);
    i2 = new(100);

    // Workaround: access the queue property directly instead of using methods
    c.items.push_back(i1);
    c.items.push_back(i2);

    // Verify size
    if (c.items.size() != 2) begin
      $display("FAILED: Expected size 2, got %0d", c.items.size());
      $finish;
    end

    // Retrieve and verify
    retrieved = c.items[0];
    if (retrieved.value != 42) begin
      $display("FAILED: Expected first item value 42, got %0d", retrieved.value);
      $finish;
    end

    retrieved = c.items[1];
    if (retrieved.value != 100) begin
      $display("FAILED: Expected second item value 100, got %0d", retrieved.value);
      $finish;
    end

    $display("PASSED");
  end
endmodule
