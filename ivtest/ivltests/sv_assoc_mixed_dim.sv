// Test associative array with mixed dimensions: assoc[int][1]
// This mimics the AXI4 strobe_data pattern
module test;
  parameter WIDTH = 4;

  // Associative array with int key, second dimension is fixed [1]
  bit [WIDTH-1:0] strobe_data[int][1];
  bit [WIDTH-1:0] val;

  initial begin
    $display("Test: assoc array with fixed second dimension");

    // Write to associative array using int key WIDTH (which is 4)
    strobe_data[WIDTH][0] = 4'hF;
    val = strobe_data[WIDTH][0];
    $display("strobe_data[%0d][0] = %h", WIDTH, val);

    // Write to another key
    strobe_data[10][0] = 4'hA;
    val = strobe_data[10][0];
    $display("strobe_data[10][0] = %h", val);

    // Verify values
    val = strobe_data[WIDTH][0];
    if (val == 4'hF) begin
      $display("strobe_data[WIDTH][0] check: PASSED");
    end else begin
      $display("strobe_data[WIDTH][0] check: FAILED (got %h)", val);
    end

    val = strobe_data[10][0];
    if (val == 4'hA) begin
      $display("strobe_data[10][0] check: PASSED");
    end else begin
      $display("strobe_data[10][0] check: FAILED (got %h)", val);
    end

    $display("PASSED");
    $finish;
  end
endmodule
