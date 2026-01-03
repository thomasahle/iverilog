// Test method calls on queue elements
// This is a common UVM pattern: q[i].method()

class item;
  int value;
  string name;

  function new(int v, string n);
    value = v;
    name = n;
  endfunction

  function string to_string();
    return $sformatf("%s=%0d", name, value);
  endfunction

  function int get_value();
    return value;
  endfunction
endclass

module test;
  item q[$];
  int errors = 0;

  initial begin
    item it;

    // Create and add items
    it = new(10, "A");
    q.push_back(it);
    it = new(20, "B");
    q.push_back(it);
    it = new(30, "C");
    q.push_back(it);

    // Direct method call on queue element
    $display("Queue contents using direct method calls:");
    for (int i = 0; i < q.size(); i++) begin
      $display("  [%0d] %s", i, q[i].to_string());
    end

    // Direct property access on queue element (should also work)
    if (q[0].value != 10) begin
      $display("FAILED: q[0].value is %0d, expected 10", q[0].value);
      errors++;
    end

    // Method returning value
    if (q[1].get_value() != 20) begin
      $display("FAILED: q[1].get_value() is %0d, expected 20", q[1].get_value());
      errors++;
    end

    // Chained access
    $display("Final element: %s", q[q.size()-1].to_string());

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
