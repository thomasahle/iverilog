// Test null comparison for dynamic array elements of class type
// Tests the %test_nul/dar opcode

class item;
  int value;
  function new(int v = 0);
    value = v;
  endfunction
endclass

class container;
  item items[];

  function new();
    items = new[3];
    // items[0] = null (default)
    items[1] = new(42);
    // items[2] = null (default)
  endfunction
endclass

module test;
  initial begin
    automatic container c = new();
    automatic int passed = 1;

    // Test null comparisons on darray elements
    if (c.items[0] != null) begin
      $display("FAILED: items[0] should be null");
      passed = 0;
    end

    if (c.items[1] == null) begin
      $display("FAILED: items[1] should not be null");
      passed = 0;
    end

    if (c.items[2] != null) begin
      $display("FAILED: items[2] should be null");
      passed = 0;
    end

    // Test the non-null element value
    if (c.items[1].value != 42) begin
      $display("FAILED: items[1].value should be 42, got %0d", c.items[1].value);
      passed = 0;
    end

    // Assign to null element and verify
    c.items[0] = new(100);
    if (c.items[0] == null) begin
      $display("FAILED: items[0] should not be null after assignment");
      passed = 0;
    end
    if (c.items[0].value != 100) begin
      $display("FAILED: items[0].value should be 100, got %0d", c.items[0].value);
      passed = 0;
    end

    // Set element back to null
    c.items[0] = null;
    if (c.items[0] != null) begin
      $display("FAILED: items[0] should be null after null assignment");
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    $finish;
  end
endmodule
