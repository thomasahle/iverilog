// Test case inside statement with X/Z wildcards
module test;
  int errors = 0;
  logic [7:0] val;
  int result;

  initial begin
    // Test case inside with X wildcard in pattern
    // X in the pattern matches any value in that position
    val = 8'b0000_1111;
    case (val) inside
      8'b0000_xxxx: result = 1;  // X in pattern = don't care
      8'b1111_xxxx: result = 2;
      default: result = 0;
    endcase
    if (result != 1) begin errors++; $display("FAIL: val=0F with 0000_xxxx pattern, result=%0d, expected 1", result); end

    val = 8'b0000_0000;
    case (val) inside
      8'b0000_xxxx: result = 1;
      default: result = 0;
    endcase
    if (result != 1) begin errors++; $display("FAIL: val=00 with 0000_xxxx pattern, result=%0d, expected 1", result); end

    val = 8'b1111_1010;
    case (val) inside
      8'b0000_xxxx: result = 1;
      8'b1111_xxxx: result = 2;
      default: result = 0;
    endcase
    if (result != 2) begin errors++; $display("FAIL: val=FA with 1111_xxxx pattern, result=%0d, expected 2", result); end

    // Test case inside with Z wildcard in pattern
    val = 8'b0101_0101;
    case (val) inside
      8'b0101_????: result = 3;  // ? (Z) in pattern = don't care
      default: result = 0;
    endcase
    if (result != 3) begin errors++; $display("FAIL: val=55 with 0101_???? pattern, result=%0d, expected 3", result); end

    // Test that value X doesn't affect regular comparisons in a bad way
    // (value X is unknown, so comparison should fail unless pattern has X)
    val = 8'bxxxx_xxxx;  // Value is all X
    case (val) inside
      8'b0000_0000: result = 1;  // Should NOT match because val is X
      8'bxxxx_xxxx: result = 2;  // X in pattern should match
      default: result = 0;
    endcase
    // Note: When value has X bits, the behavior is implementation-defined
    // but with wildcard equality (==?), X in the pattern matches anything
    if (result != 2) begin errors++; $display("FAIL: val=XX with xxxx pattern, result=%0d, expected 2", result); end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end
endmodule
