// Test class copy semantics
class data;
  int value;
  int arr[4];

  function new(int v = 0);
    value = v;
    arr[0] = 1;
    arr[1] = 2;
    arr[2] = 3;
    arr[3] = 4;
  endfunction

  function data copy();
    data d = new();
    d.value = this.value;
    // Copy array element by element
    for (int i = 0; i < 4; i++)
      d.arr[i] = this.arr[i];
    return d;
  endfunction
endclass

module test;
  data d1, d2, d3;
  int errors = 0;

  initial begin
    // Create original
    d1 = new(42);

    // Test reference assignment (shallow copy)
    d2 = d1;
    d1.value = 100;
    if (d2.value != 100) begin
      $display("FAILED: reference assignment - d2.value=%0d, expected 100", d2.value);
      errors++;
    end

    // Test copy method (deep copy)
    d1.value = 42;
    d3 = d1.copy();
    d1.value = 200;
    if (d3.value != 42) begin
      $display("FAILED: copy method - d3.value=%0d, expected 42", d3.value);
      errors++;
    end

    // Test array copy in copy method
    if (d3.arr[0] != 1 || d3.arr[3] != 4) begin
      $display("FAILED: array copy - d3.arr[0]=%0d, d3.arr[3]=%0d", d3.arr[0], d3.arr[3]);
      errors++;
    end

    // Modify original array, copied should be independent
    d1.arr[0] = 99;
    if (d3.arr[0] == 99) begin
      $display("FAILED: arrays should be independent - d3.arr[0]=%0d", d3.arr[0]);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
