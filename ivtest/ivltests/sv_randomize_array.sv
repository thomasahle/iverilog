// Test randomize() on array element - call randomize on dynamic array element

class item_class;
  rand int value;
  rand logic [7:0] data;

  function new();
    value = 0;
    data = 0;
  endfunction
endclass

class container_class;
  item_class items[];

  function new();
    items = new[3];
    items[0] = new();
    items[1] = new();
    items[2] = new();
  endfunction

  function int test();
    int passed = 1;

    // Call randomize on each array element
    foreach(items[i]) begin
      if (!items[i].randomize()) begin
        $display("FAILED: items[%0d].randomize() returned 0", i);
        passed = 0;
      end else begin
        $display("items[%0d].randomize succeeded: value=%0d, data=%0d", i, items[i].value, items[i].data);
      end
    end

    // Verify values changed (not all zero after randomize)
    if (items[0].value == 0 && items[1].value == 0 && items[2].value == 0) begin
      // Very unlikely all three are zero after randomize unless broken
      $display("Warning: All values are 0 after randomize");
    end

    return passed;
  endfunction
endclass

module test;
  initial begin
    container_class container;
    container = new();

    if (container.test()) begin
      $display("PASSED");
    end else begin
      $display("FAILED");
    end
    $finish;
  end
endmodule
