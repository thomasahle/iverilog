// Test dynamic array element assignment with width mismatch
// This tests the fix for assertion failure when storing values
// of different widths to dynamic array elements.

module test;
  logic [31:0] darray[];
  logic [15:0] small_val;
  logic [47:0] large_val;
  logic [31:0] exact_val;

  initial begin
    // Initialize array
    darray = new[3];

    // Store exact width - should work
    exact_val = 32'hDEADBEEF;
    darray[0] = exact_val;
    if (darray[0] !== 32'hDEADBEEF) begin
      $display("FAILED: exact width assignment");
      $finish;
    end

    // Store smaller value - should be zero-extended
    small_val = 16'hABCD;
    darray[1] = small_val;
    if (darray[1] !== 32'h0000ABCD) begin
      $display("FAILED: small value assignment, got %h", darray[1]);
      $finish;
    end

    // Store larger value - should be truncated
    large_val = 48'h123456789ABC;
    darray[2] = large_val;
    if (darray[2] !== 32'h56789ABC) begin
      $display("FAILED: large value assignment, got %h", darray[2]);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
