// Test string value formatting (vpiDecStrVal, vpiHexStrVal, vpiBinStrVal)
// This tests the VPI string stack get_value formats
module test;
  string s;
  int errors;

  initial begin
    errors = 0;

    // Test with simple string
    s = "A";
    $display("String 'A':");
    $display("  String: %s", s);
    $display("  Decimal: %d", s);  // ASCII 65 -> "65"
    $display("  Hex: %h", s);      // 0x41

    // Test with 2-char string
    s = "AB";
    $display("String 'AB':");
    $display("  String: %s", s);
    $display("  Decimal: %d", s);  // 'A'*256 + 'B' = 65*256 + 66 = 16706
    $display("  Hex: %h", s);      // 0x4142

    // Test with empty string
    s = "";
    $display("Empty string:");
    $display("  String: '%s'", s);
    $display("  Decimal: %d", s);  // 0
    $display("  Hex: %h", s);      // empty

    // Test with longer string
    s = "Hello";
    $display("String 'Hello':");
    $display("  String: %s", s);
    $display("  Hex: %h", s);      // 48656c6c6f

    // If we get here without errors, the test passed
    $display("PASSED");
  end
endmodule
