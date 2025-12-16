// Test foreach on dynamic arrays of class objects

class simple_class;
  int value;
  function new(int v = 0);
    value = v;
  endfunction
endclass

module test;
  initial begin
    simple_class arr[];
    int sum;

    // Create array
    arr = new[3];
    arr[0] = new(10);
    arr[1] = new(20);
    arr[2] = new(30);

    // Test foreach iteration
    sum = 0;
    foreach(arr[i]) begin
      $display("arr[%0d].value = %0d", i, arr[i].value);
      sum = sum + arr[i].value;
    end

    if (sum == 60) begin
      $display("PASSED");
    end else begin
      $display("FAILED: sum = %0d, expected 60", sum);
    end
  end
endmodule
