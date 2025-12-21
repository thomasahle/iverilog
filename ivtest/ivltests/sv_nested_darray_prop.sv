// Test nested darray property access
// Pattern: outer_h.items[i].value = x; and reading outer_h.items[i].value
// This is a common UVM pattern for accessing configuration in nested class hierarchies

class Inner;
  bit value;
  int count;

  function new();
    value = 0;
    count = 0;
  endfunction
endclass

class Outer;
  Inner items[];

  function new();
    items = new[3];
    items[0] = new();
    items[1] = new();
    items[2] = new();
  endfunction
endclass

class Container;
  Outer outer_h;

  function new();
    outer_h = new();
  endfunction

  function void test_write();
    // Test writing to nested darray property with constant value
    outer_h.items[0].value = 1;
    outer_h.items[1].value = 0;
    outer_h.items[2].value = 1;

    // Test writing integer property
    outer_h.items[0].count = 100;
    outer_h.items[1].count = 200;
    outer_h.items[2].count = 300;
  endfunction

  function int test_read();
    int errors = 0;

    // Test reading nested darray properties
    if (outer_h.items[0].value !== 1) begin
      $display("FAILED: items[0].value = %0d, expected 1", outer_h.items[0].value);
      errors++;
    end
    if (outer_h.items[1].value !== 0) begin
      $display("FAILED: items[1].value = %0d, expected 0", outer_h.items[1].value);
      errors++;
    end
    if (outer_h.items[2].value !== 1) begin
      $display("FAILED: items[2].value = %0d, expected 1", outer_h.items[2].value);
      errors++;
    end

    if (outer_h.items[0].count !== 100) begin
      $display("FAILED: items[0].count = %0d, expected 100", outer_h.items[0].count);
      errors++;
    end
    if (outer_h.items[1].count !== 200) begin
      $display("FAILED: items[1].count = %0d, expected 200", outer_h.items[1].count);
      errors++;
    end
    if (outer_h.items[2].count !== 300) begin
      $display("FAILED: items[2].count = %0d, expected 300", outer_h.items[2].count);
      errors++;
    end

    return errors;
  endfunction
endclass

module test;
  Container c;
  int errors;

  initial begin
    c = new();
    c.test_write();
    errors = c.test_read();

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end
endmodule
