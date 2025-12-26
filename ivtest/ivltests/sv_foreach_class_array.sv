// Test foreach on class array property

class data_container;
  int data[4];
  logic [7:0] bytes[8];

  function new();
    for (int i = 0; i < 4; i++) data[i] = i * 10;
    for (int i = 0; i < 8; i++) bytes[i] = i * 5;
  endfunction

  // Foreach inside class method
  function int sum_data();
    automatic int total = 0;
    foreach(data[i]) begin
      total = total + data[i];
    end
    return total;
  endfunction

  function int sum_bytes();
    automatic int total = 0;
    foreach(bytes[i]) begin
      total = total + bytes[i];
    end
    return total;
  endfunction
endclass

module test;
  initial begin
    automatic data_container dc;
    automatic int sum1, sum2;
    automatic int expected1, expected2;

    dc = new();

    // Expected: 0 + 10 + 20 + 30 = 60
    expected1 = 60;
    sum1 = dc.sum_data();
    $display("sum_data() = %0d (expected %0d)", sum1, expected1);

    // Expected: 0 + 5 + 10 + 15 + 20 + 25 + 30 + 35 = 140
    expected2 = 140;
    sum2 = dc.sum_bytes();
    $display("sum_bytes() = %0d (expected %0d)", sum2, expected2);

    if (sum1 == expected1 && sum2 == expected2)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
