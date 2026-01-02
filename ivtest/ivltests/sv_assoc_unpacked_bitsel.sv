// Test bit-select on associative array with additional unpacked dimensions
// e.g., bit [7:0] data[int][1];  data[key][0][idx] = 1'b1;
// This specifically tests variable bit-select index (non-constant)
// NOTE: This test verifies elaboration works. VVP runtime support is partial.

module test;
  parameter WIDTH = 8;
  bit [WIDTH-1:0] strobe_data[int][1];  // Assoc + unpacked [1] + packed [7:0]
  int key = 5;
  int pass = 1;

  initial begin
    // Initialize element using the variable key
    strobe_data[key][0] = 8'h00;
    $display("Initial: strobe_data[%0d][0] = %h", key, strobe_data[key][0]);

    // Test bit-select lvalue with variable index (this is what AXI4 uses)
    for (int i = 0; i < 4; i++) begin
      strobe_data[key][0][i] = 1'b1;
    end
    $display("After loop: strobe_data[%0d][0] = %h (expected 0F)", key, strobe_data[key][0]);
    if (strobe_data[key][0] != 8'h0F) pass = 0;

    // Test clearing bits with variable index
    for (int i = 0; i < 2; i++) begin
      strobe_data[key][0][i] = 1'b0;
    end
    $display("After clear: strobe_data[%0d][0] = %h (expected 0C)", key, strobe_data[key][0]);
    if (strobe_data[key][0] != 8'h0C) pass = 0;

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
