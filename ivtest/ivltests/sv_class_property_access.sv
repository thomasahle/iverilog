// Test various class property access patterns
// Verifies: nested property access, queue property methods

module test;

  class Inner;
    int value;
    bit [7:0] data;

    function new();
      value = 42;
      data = 8'hAB;
    endfunction
  endclass

  class Outer;
    Inner inner;
    int counter;
    bit [7:0] items[$];

    function new();
      inner = new();
      counter = 0;
    endfunction

    function void add_item(bit [7:0] item);
      items.push_back(item);
      counter++;
    endfunction

    function int get_item_count();
      return items.size();
    endfunction
  endclass

  initial begin
    Outer obj;
    int i;

    obj = new();

    // Test nested property access
    if (obj.inner.value != 42) begin
      $display("FAILED: inner.value = %0d, expected 42", obj.inner.value);
      $finish;
    end
    $display("Nested access: obj.inner.value = %0d", obj.inner.value);

    // Test nested property modification
    obj.inner.value = 100;
    if (obj.inner.value != 100) begin
      $display("FAILED: inner.value = %0d after modification", obj.inner.value);
      $finish;
    end

    // Test queue property methods
    obj.add_item(8'h10);
    obj.add_item(8'h20);
    obj.add_item(8'h30);

    if (obj.items.size() != 3) begin
      $display("FAILED: items.size() = %0d, expected 3", obj.items.size());
      $finish;
    end

    if (obj.counter != 3) begin
      $display("FAILED: counter = %0d, expected 3", obj.counter);
      $finish;
    end

    // Test queue element access
    for (i = 0; i < obj.items.size(); i++) begin
      $display("items[%0d] = %h", i, obj.items[i]);
    end

    if (obj.items[0] != 8'h10 || obj.items[1] != 8'h20 || obj.items[2] != 8'h30) begin
      $display("FAILED: Queue element values incorrect");
      $finish;
    end

    $display("All property access patterns working");
    $display("PASSED");
    $finish;
  end

endmodule
