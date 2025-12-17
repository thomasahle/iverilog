// Test class array indexing with nested method calls
// Tests: arr[i].property.method() pattern

class inner_class;
  int value;

  function new();
    value = 0;
  endfunction

  function void set_val(int v);
    value = v;
  endfunction

  function int get_val();
    return value;
  endfunction
endclass

class outer_class;
  inner_class inner;

  function new();
    inner = new();
  endfunction
endclass

module test;
  outer_class arr[3];
  int result;
  int errors = 0;

  initial begin
    // Initialize array elements
    arr[0] = new();
    arr[1] = new();
    arr[2] = new();

    // Test task calls through nested property (constant indices)
    arr[0].inner.set_val(100);
    arr[1].inner.set_val(200);
    arr[2].inner.set_val(300);

    // Test function calls through nested property (constant indices)
    result = arr[0].inner.get_val();
    if (result != 100) begin
      $display("FAILED: arr[0].inner.get_val() = %0d, expected 100", result);
      errors++;
    end

    result = arr[1].inner.get_val();
    if (result != 200) begin
      $display("FAILED: arr[1].inner.get_val() = %0d, expected 200", result);
      errors++;
    end

    result = arr[2].inner.get_val();
    if (result != 300) begin
      $display("FAILED: arr[2].inner.get_val() = %0d, expected 300", result);
      errors++;
    end

    // Test with variable index in for loop
    for (int i = 0; i < 3; i++) begin
      arr[i].inner.set_val(i * 100);
    end

    for (int i = 0; i < 3; i++) begin
      result = arr[i].inner.get_val();
      if (result != i * 100) begin
        $display("FAILED: arr[%0d].inner.get_val() = %0d, expected %0d",
                 i, result, i * 100);
        errors++;
      end
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
    $finish;
  end
endmodule
