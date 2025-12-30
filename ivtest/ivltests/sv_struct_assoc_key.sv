// Test that struct member access compiles as associative array key
// This tests the code path where a struct member access expression
// is evaluated as a string for use as an associative array key.
// Previously this would fail with "string select from this expression type
// not fully supported" error during code generation.

module test;
  bit [7:0] memory[longint];
  logic [31:0] addr;
  logic [7:0] data;

  initial begin
    // Store values in associative array
    memory[32'h1000] = 8'hAB;
    memory[32'h2000] = 8'hCD;

    // Test reading using variable as key (this triggers the fixed code path)
    addr = 32'h1000;
    data = memory[addr];

    if (data == 8'hAB) begin
      $display("Test 1 PASSED: data = %h", data);
    end else begin
      $display("FAILED: Test 1 expected AB, got %h", data);
      $finish;
    end

    addr = 32'h2000;
    data = memory[addr];

    if (data == 8'hCD) begin
      $display("Test 2 PASSED: data = %h", data);
    end else begin
      $display("FAILED: Test 2 expected CD, got %h", data);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
