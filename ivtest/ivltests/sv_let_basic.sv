module test;
  let double(x) = x * 2;
  let add(a, b) = a + b;

  initial begin
    int result;
    result = double(5);
    $display("double(5) = %0d", result);

    result = add(3, 7);
    $display("add(3, 7) = %0d", result);

    $display("PASSED");
  end
endmodule
