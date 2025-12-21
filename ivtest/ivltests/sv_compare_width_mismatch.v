// Test that comparison operations handle width mismatches gracefully
// The VVP comparison opcodes should not crash on mismatched widths

`timescale 1ns/10ps

module test;
  reg [7:0] val8;
  reg [31:0] val32;
  reg [15:0] val16;
  reg result;
  integer errors;

  initial begin
    errors = 0;
    val8 = 8'hFF;
    val32 = 32'h000000FF;
    val16 = 16'h00FF;

    // Equality tests
    if (val8 == val32[7:0]) begin
    end else begin
      $display("FAILED: val8 == val32[7:0]");
      errors = errors + 1;
    end

    // Less than tests
    if (val8 < 16'h0100) begin
    end else begin
      $display("FAILED: val8 < 16'h0100");
      errors = errors + 1;
    end

    // Case equality
    result = (val8 === 8'hFF);
    if (result !== 1'b1) begin
      $display("FAILED: val8 === 8'hFF");
      errors = errors + 1;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end
endmodule
