// Test simple method call on queue element

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
  item q[$];
  item it;
  int result;
  int errors = 0;

  initial begin
    // Create and add items
    it = new(100);
    q.push_back(it);

    // Direct method call on queue element
    result = q[0].get_value();
    if (result != 100) begin
      $display("FAILED: result = %0d, expected 100", result);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
