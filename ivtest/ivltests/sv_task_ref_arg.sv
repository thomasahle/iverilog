// Test task with ref argument (scalar types)
module test;
  int value;
  int arr[4];
  int errors = 0;

  task automatic swap(ref int a, ref int b);
    int tmp;
    tmp = a;
    a = b;
    b = tmp;
  endtask

  task automatic increment(ref int x);
    x++;
  endtask

  task automatic add_to(ref int x, input int delta);
    x = x + delta;
  endtask

  initial begin
    // Test swap
    value = 10;
    arr[0] = 5;
    swap(value, arr[0]);
    if (value != 5 || arr[0] != 10) begin
      $display("FAILED: after swap value=%0d, arr[0]=%0d", value, arr[0]);
      errors++;
    end

    // Test increment
    value = 42;
    increment(value);
    if (value != 43) begin
      $display("FAILED: after increment value=%0d", value);
      errors++;
    end

    // Test add_to with ref and input
    value = 100;
    add_to(value, 50);
    if (value != 150) begin
      $display("FAILED: after add_to value=%0d", value);
      errors++;
    end

    // Test ref with array element
    arr[1] = 20;
    increment(arr[1]);
    if (arr[1] != 21) begin
      $display("FAILED: after increment arr[1]=%0d", arr[1]);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
