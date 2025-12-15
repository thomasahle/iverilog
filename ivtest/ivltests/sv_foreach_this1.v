// Test foreach with this.array syntax
// IEEE 1800-2017 12.7.3 - foreach with hierarchical array identifier

class Container;
  int arr[4];

  function new();
    arr[0] = 10;
    arr[1] = 20;
    arr[2] = 30;
    arr[3] = 40;
  endfunction

  function void print_arr();
    // Test foreach with explicit this.arr
    foreach(this.arr[i])
      $display("this.arr[%0d] = %0d", i, this.arr[i]);
  endfunction

  function int sum();
    int s = 0;
    // Test foreach with this.arr in expression context
    foreach(this.arr[i])
      s += this.arr[i];
    return s;
  endfunction
endclass

module test;
  Container c;
  int errors = 0;

  initial begin
    c = new();
    c.print_arr();
    $display("sum = %0d", c.sum());

    if (c.sum() != 100) begin
      $display("FAILED: expected sum=100, got %0d", c.sum());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    $finish;
  end
endmodule
