// Test $cast in parameterized class methods
// This tests the fix for uvm_driver.get_next_item() where base class
// objects need to be cast to derived types in parameterized methods.

class base_item;
  int id;
  function new(int i = 0);
    id = i;
  endfunction
endclass

class derived_item extends base_item;
  string name;
  function new(int i = 0, string n = "");
    super.new(i);
    name = n;
  endfunction
endclass

// Parameterized container class similar to uvm_driver
class container #(type T = base_item);
  T stored_item;

  function void store_base(base_item item);
    // This is the pattern that was failing - cast base to derived
    void'($cast(stored_item, item));
  endfunction

  function T get_stored();
    return stored_item;
  endfunction
endclass

module test;
  initial begin
    container #(derived_item) c;
    derived_item d, result;
    base_item b;

    c = new();
    d = new(42, "test_item");
    b = d;  // Upcast to base

    // Store via base class (tests $cast in parameterized method)
    c.store_base(b);

    // Retrieve and verify
    result = c.get_stored();
    if (result == null) begin
      $display("FAILED: stored_item is null");
      $finish;
    end

    if (result.id != 42) begin
      $display("FAILED: id mismatch, got %0d expected 42", result.id);
      $finish;
    end

    if (result.name != "test_item") begin
      $display("FAILED: name mismatch, got '%s' expected 'test_item'", result.name);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
