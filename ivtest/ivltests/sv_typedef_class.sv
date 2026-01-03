// Test typedef with class and forward declaration
typedef class item;

class container;
  item items[$];

  function void add(item i);
    items.push_back(i);
  endfunction

  function int count();
    return items.size();
  endfunction
endclass

class item;
  int value;
  string name;

  function new(int v, string n);
    value = v;
    name = n;
  endfunction
endclass

module test;
  container c;
  item i1, i2;
  int errors = 0;

  initial begin
    c = new();
    i1 = new(10, "first");
    i2 = new(20, "second");

    c.add(i1);
    c.add(i2);

    if (c.count() != 2) begin
      $display("FAILED: count = %0d, expected 2", c.count());
      errors++;
    end

    // Access items through container
    if (c.items[0].value != 10) begin
      $display("FAILED: items[0].value = %0d", c.items[0].value);
      errors++;
    end
    if (c.items[1].name != "second") begin
      $display("FAILED: items[1].name = %s", c.items[1].name);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
