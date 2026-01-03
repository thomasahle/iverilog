// Test printing queue of class objects
// Verifies queue iteration and class method calls on elements

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

    // Check size
    if (q.size() != 3) begin
      $display("FAILED: queue size is %0d, expected 3", q.size());
      errors++;
    end

    // Iterate and print using temp variable
    $display("Queue contents:");
    for (int i = 0; i < q.size(); i++) begin
      it = q[i];
      $display("  [%0d] %s", i, it.to_string());
    end

    // Verify values
    if (q[0].value != 10 || q[1].value != 20 || q[2].value != 30) begin
      $display("FAILED: incorrect values");
      errors++;
    end

    // Pop and verify
    it = q.pop_front();
    if (it.value != 10) begin
      $display("FAILED: pop_front returned wrong item");
      errors++;
    end

    if (q.size() != 2) begin
      $display("FAILED: size after pop is %0d, expected 2", q.size());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
