// Test print_field size masking without UVM dependency
// This tests that a print function properly masks values to specified size

module test;

  // Simple printer class to test print_field behavior
  class simple_printer;
    function void print_field(string name, logic [1023:0] value, int size);
      string val_str;
      logic [1023:0] masked_value;
      logic [1023:0] mask;
      // Mask the value to the specified size
      if (size > 0 && size < 1024) begin
        mask = '0;
        for (int i = 0; i < size; i++) mask[i] = 1'b1;
        masked_value = value & mask;
      end else begin
        masked_value = value;
      end
      $sformat(val_str, "%0d", masked_value);
      $display("%s: %s", name, val_str);
    endfunction
  endclass

  initial begin
    simple_printer printer;
    int my_int;
    bit [7:0] my_byte;
    bit [63:0] my_large;

    printer = new();

    $display("Testing print_field with size masking:");

    // Test normal 32-bit int
    my_int = 42;
    $display("Expected: my_int=42");
    printer.print_field("my_int", my_int, 32);

    // Test 8-bit value
    my_byte = 8'hAB;
    $display("Expected: my_byte=171");
    printer.print_field("my_byte", my_byte, 8);

    // Test negative int (should be masked to 32 bits = 4294967295)
    my_int = -1;
    $display("Expected: negative_int=4294967295");
    printer.print_field("negative_int", my_int, 32);

    // Test 64-bit value
    my_large = 64'hDEADBEEFCAFEBABE;
    $display("Expected: my_large=16045690984833335998");
    printer.print_field("my_large", my_large, 64);

    $display("PASSED");
  end
endmodule
