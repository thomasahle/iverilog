// Test foreach on dynamic array class properties
// IEEE 1800-2017 12.7.3 - foreach loop

class Container;
  int arr[];

  function new();
    arr = new[3];
    arr[0] = 10;
    arr[1] = 20;
    arr[2] = 30;
  endfunction

  function void print_arr();
    foreach (arr[i]) begin
      $display("arr[%0d] = %0d", i, arr[i]);
    end
  endfunction

  function int sum();
    int total;
    total = 0;
    foreach (arr[i]) begin
      total = total + arr[i];
    end
    return total;
  endfunction
endclass

module test;
  Container c;
  int errors;

  initial begin
    errors = 0;
    c = new();
    c.print_arr();

    if (c.sum() != 60) begin
      $display("FAILED: expected sum=60, got %0d", c.sum());
      errors = errors + 1;
    end

    if (errors == 0)
      $display("PASSED");
    $finish;
  end
endmodule
