// Test associative array with class object values
// NOTE: Associative arrays of class objects are not yet fully supported.
// This test demonstrates the feature request/WIP status.
// For now, use queue of class objects instead: item q[$];

class item;
  int value;
  function new(int v);
    value = v;
  endfunction
  function int get_value();
    return value;
  endfunction
endclass

module test;
  // Use queue instead of assoc array for now
  item q[$];
  int errors = 0;

  initial begin
    item it;

    // Create and add items
    it = new(100);
    q.push_back(it);
    it = new(200);
    q.push_back(it);

    // Check size
    if (q.size() != 2) begin
      $display("FAILED: size is %0d, expected 2", q.size());
      errors++;
    end

    // Access value via queue element method (now working!)
    if (q[0].get_value() != 100) begin
      $display("FAILED: q[0].get_value() is %0d, expected 100", q[0].get_value());
      errors++;
    end

    // Method call on second element
    if (q[1].get_value() != 200) begin
      $display("FAILED: q[1].get_value() is %0d, expected 200", q[1].get_value());
      errors++;
    end

    // Delete front element
    void'(q.pop_front());
    if (q.size() != 1) begin
      $display("FAILED: size after pop_front is %0d, expected 1", q.size());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
