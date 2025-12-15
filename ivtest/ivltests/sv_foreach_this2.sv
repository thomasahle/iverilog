// Test foreach with this.array in different contexts
// Tests nested class, multiple arrays, and method calls

class Container;
  int data[4];
  byte bytes[8];

  function new();
    int i;
    for (i = 0; i < 4; i++) data[i] = i * 10;
    for (i = 0; i < 8; i++) bytes[i] = i;
  endfunction

  // Test foreach in a method
  function int sum_data();
    int total = 0;
    foreach (this.data[i]) begin
      total = total + this.data[i];
    end
    return total;
  endfunction

  // Test foreach with multiple arrays
  function int sum_all();
    int total = 0;
    foreach (this.data[i]) begin
      total = total + this.data[i];
    end
    foreach (this.bytes[j]) begin
      total = total + this.bytes[j];
    end
    return total;
  endfunction

  // Test foreach with modification
  function void double_data();
    foreach (this.data[i]) begin
      this.data[i] = this.data[i] * 2;
    end
  endfunction
endclass

module test;
  Container c;
  int sum;

  initial begin
    c = new();

    // Test sum_data (0 + 10 + 20 + 30 = 60)
    sum = c.sum_data();
    if (sum != 60) begin
      $display("FAILED: sum_data() returned %0d, expected 60", sum);
      $finish;
    end

    // Test sum_all (60 + 0+1+2+3+4+5+6+7 = 60 + 28 = 88)
    sum = c.sum_all();
    if (sum != 88) begin
      $display("FAILED: sum_all() returned %0d, expected 88", sum);
      $finish;
    end

    // Test double_data
    c.double_data();
    sum = c.sum_data();
    if (sum != 120) begin
      $display("FAILED: After double_data(), sum is %0d, expected 120", sum);
      $finish;
    end

    $display("PASSED");
  end
endmodule
