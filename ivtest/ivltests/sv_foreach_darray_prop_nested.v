// Test foreach on dynamic array class properties with nested access
// Tests accessing arr[i].member inside foreach body

class Item;
  int value;
  string name;

  function new(int v, string n);
    value = v;
    name = n;
  endfunction
endclass

class Container;
  Item items[];

  function new();
    items = new[3];
    items[0] = new(10, "first");
    items[1] = new(20, "second");
    items[2] = new(30, "third");
  endfunction

  // Test foreach with nested member access
  function int sum_values();
    int total;
    total = 0;
    foreach (items[i]) begin
      total = total + items[i].value;
    end
    return total;
  endfunction

  // Test foreach with string property access
  function void print_names();
    foreach (items[i]) begin
      $display("items[%0d].name = %s", i, items[i].name);
    end
  endfunction

  // Test foreach with modification
  function void double_values();
    foreach (items[i]) begin
      items[i].value = items[i].value * 2;
    end
  endfunction
endclass

module test;
  Container c;
  int errors;

  initial begin
    errors = 0;
    c = new();

    // Test 1: Sum values
    if (c.sum_values() !== 60) begin
      $display("FAILED: Test 1 - sum = %0d, expected 60", c.sum_values());
      errors = errors + 1;
    end

    // Test 2: Print names (visual check)
    $display("Printing names:");
    c.print_names();

    // Test 3: Double values and check
    c.double_values();
    if (c.sum_values() !== 120) begin
      $display("FAILED: Test 3 - sum after double = %0d, expected 120", c.sum_values());
      errors = errors + 1;
    end

    if (errors == 0)
      $display("PASSED");
  end
endmodule
