// Test %p format specifier for $sformatf
// %p is used to print values in assignment pattern format

module test;
  logic [31:0] data;
  logic [7:0] byte_val;
  int int_val;
  string str;

  initial begin
    data = 32'h12345678;
    byte_val = 8'hAB;
    int_val = 42;

    // Test %p with different types
    str = $sformatf("Data: %p", data);
    $display("32-bit value: %s", str);

    str = $sformatf("Byte: %p", byte_val);
    $display("8-bit value: %s", str);

    str = $sformatf("Int: %p", int_val);
    $display("int value: %s", str);

    // Test with width specifier
    str = $sformatf("Padded: %10p", data);
    $display("Padded value: '%s'", str);

    // Test negative values
    int_val = -123;
    str = $sformatf("Negative: %p", int_val);
    $display("Negative: %s", str);

    $display("PASSED");
  end
endmodule
